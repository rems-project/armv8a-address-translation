(*<*)
(* Author: Thomas Bauereiss *)
theory Address_Translation_Pure
  imports AArch64_Aux Address_Translation_Orig
begin
(*>*)

section \<open>Pure characterisation\<close>

subsection \<open>Types\<close>

text \<open>Translation tables are represented as a list of entries, each of which might recursively
contain another table.\<close>

datatype TableEntry =
  Invalid
  | Descriptor "64 word" (* 64-bit block or page descriptor *)
  | Table "52 word" bool bool bool bool bool "TableEntry list" (* base address, table attributes, entries *)

text \<open>A record for the main parameters of the translation, e.g. address size or page size.\<close>

record Parameters =
  inputsize :: int
  outputsize :: int
  grainsize :: int
  firstblocklevel :: int
  updateAF :: bool
  SH :: "2 word"
  ORGN :: "2 word"
  IRGN :: "2 word"

subsection \<open>Auxiliary functions for our pure characterisation, e.g. for reading the translation
parameters from the control registers or decoding descriptor attributes.\<close>

definition read_params :: "bool \<Rightarrow> regstate sequential_state \<Rightarrow> Parameters" where
  "read_params high s =
     (let
        largegrain = (if high then Word.slice 30 (TCR_EL1 (regstate s)) = (3 :: 2 word)
                      else Word.slice 14 (TCR_EL1 (regstate s)) = (1 :: 2 word));
        midgrain = (if high then Word.slice 30 (TCR_EL1 (regstate s)) = (1 :: 2 word)
                    else Word.slice 14 (TCR_EL1 (regstate s)) = (2 :: 2 word));
        grainsize = (if largegrain then 16 else if midgrain then 14 else 12);
        outputsize = calc_outputsize (Word.slice 32 (TCR_EL1 (regstate s))) largegrain;
        inputsize_max = (if largegrain then 52 else 48);
        inputsize = 64 - (uint (Word.slice (if high then 16 else 0) (TCR_EL1 (regstate s)) :: 6 word)) in
      \<lparr>inputsize = min (max inputsize 25) inputsize_max,
       outputsize = outputsize,
       grainsize = grainsize,
       firstblocklevel = (if \<not>largegrain \<and> midgrain then 2 else 1),
       updateAF = TCR_EL1 (regstate s) !! 39,
       SH = Word.slice (if high then 28 else 12) (TCR_EL1 (regstate s)),
       ORGN = Word.slice (if high then 26 else 10) (TCR_EL1 (regstate s)),
       IRGN = Word.slice (if high then 24 else 8) (TCR_EL1 (regstate s))\<rparr>)"

abbreviation "largegrain p \<equiv> (grainsize p = 16)"
abbreviation "midgrain p \<equiv> (grainsize p = 14)"

definition startlevel :: "Parameters \<Rightarrow> int" where
  "startlevel p \<equiv> calc_startlevel (inputsize p) (grainsize p) (grainsize p - 3)"

definition baselowerbound :: "Parameters \<Rightarrow> int" where
  "baselowerbound p \<equiv>
     3 + (inputsize p) - ((3 - startlevel p) * (grainsize p - 3) + (grainsize p))"

abbreviation "contiguousbitcheck p level \<equiv>
  calc_contiguousbitcheck (inputsize p) (largegrain p) (midgrain p) level"

definition baseaddress :: "64 word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 52 word" where
  "baseaddress baseregister baselowerbound_arg outputsize_arg \<equiv>
     (if outputsize_arg = 52 then
        (let z = max baselowerbound_arg 6 in
         concat_vec (Word.slice 2 baseregister :: 4 word)
                    (slice_zeros_concat 48 baseregister z (48 - z) z :: 48 word))
      else
        place_slice 52 baseregister baselowerbound_arg (48 - baselowerbound_arg) baselowerbound_arg)"

definition valid_vaddr :: "64 word \<Rightarrow> int \<Rightarrow> regstate sequential_state \<Rightarrow> bool" where
  "valid_vaddr addr addrtop s \<equiv>
     (let high = addr !! nat addrtop;
          p = read_params high s in
        (if high
         then addr AND slice_mask 64 (inputsize p) (addrtop - inputsize p + 1) =
              slice_mask 64 (inputsize p) (addrtop - inputsize p + 1)
         else addr AND slice_mask 64 (inputsize p) (addrtop - inputsize p + 1) = 0))"

abbreviation IsBlockDescriptor :: "64 word \<Rightarrow> bool" where
  "IsBlockDescriptor desc \<equiv> Word.slice 0 desc = (0b01 :: 2 word)"

definition ValidDescriptor :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow> bool" where
  "ValidDescriptor level grainsize_arg outputsize_arg desc \<equiv>
     desc !! 0 \<and>
     \<not>(IsBlockDescriptor desc \<and> level = 3) \<and>
     (\<not>IsBlockDescriptor desc \<and> level < 3 \<longrightarrow>
        (outputsize_arg < 52 \<and> grainsize_arg = 16 \<longrightarrow> Word.slice 12 desc = (0 :: 4 word)) \<and>
        (outputsize_arg < 48 \<longrightarrow> desc AND slice_mask 64 outputsize_arg (48 - outputsize_arg) = 0))"

definition read_WalkAttrDecode :: "2 word \<Rightarrow> 2 word \<Rightarrow> 2 word \<Rightarrow> bool \<Rightarrow> regstate sequential_state \<Rightarrow> MemoryAttributes" where
  "read_WalkAttrDecode SH_arg ORGN_arg IRGN_arg secondstage s \<equiv>
     \<lparr>MemoryAttributes_typ = MemType_Normal, MemoryAttributes_device = DeviceType_GRE,
             MemoryAttributes_inner =
               \<lparr>MemAttrHints_attrs =
                  if \<not> secondstage \<and> (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> IRGN_arg = 0) \<or>
                     secondstage \<and> (HCR_EL2 (regstate s) !! 32 \<or> IRGN_arg = 0)
                  then 0 else if IRGN_arg = 1 \<or> IRGN_arg \<noteq> 2 then 3 else 2,
                  MemAttrHints_hints =
                    if \<not> secondstage \<and> (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> IRGN_arg = 0) \<or>
                       secondstage \<and> (HCR_EL2 (regstate s) !! 32 \<or> IRGN_arg = 0)
                    then MemHint_No else if IRGN_arg = 1 then MemHint_RWA else MemHint_RA,
                  MemAttrHints_transient = False\<rparr>,
             MemoryAttributes_outer =
               \<lparr>MemAttrHints_attrs =
                  if \<not> secondstage \<and> (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> ORGN_arg = 0) \<or>
                     secondstage \<and> (HCR_EL2 (regstate s) !! 32 \<or> ORGN_arg = 0)
                  then 0 else if ORGN_arg = 1 \<or> ORGN_arg \<noteq> 2 then 3 else 2,
                  MemAttrHints_hints =
                    if \<not> secondstage \<and> (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> ORGN_arg = 0) \<or>
                       secondstage \<and> (HCR_EL2 (regstate s) !! 32 \<or> ORGN_arg = 0)
                    then MemHint_No else if ORGN_arg = 1 then MemHint_RWA else MemHint_RA,
                  MemAttrHints_transient = False\<rparr>,
             MemoryAttributes_shareable =
               if \<not> secondstage then read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> IRGN_arg = 0 \<and> ORGN_arg = 0 \<or> SH_arg !! Suc 0
               else (HCR_EL2 (regstate s) !! 32 \<or> IRGN_arg = 0) \<and> (HCR_EL2 (regstate s) !! 32 \<or> ORGN_arg = 0) \<or> SH_arg !! Suc 0,
             MemoryAttributes_outershareable =
               if \<not> secondstage then read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2 \<longrightarrow> IRGN_arg = 0 \<and> ORGN_arg = 0 \<or> SH_arg = 2
               else (HCR_EL2 (regstate s) !! 32 \<or> IRGN_arg = 0) \<and> (HCR_EL2 (regstate s) !! 32 \<or> ORGN_arg = 0) \<or> SH_arg = 2\<rparr>"

definition read_S1CacheDisabled :: "AccType \<Rightarrow> regstate sequential_state \<Rightarrow> bool" where
  "read_S1CacheDisabled acctype s =
     (let sctlr = read_SCTLR (read_S1TranslationRegime (read_EL s) s) s in
      if acctype = AccType_IFETCH then \<not>(sctlr !! 12) else \<not>(sctlr !! 2))"

definition read_LongConvertAttrsHints :: "4 word \<Rightarrow> AccType \<Rightarrow> regstate sequential_state \<Rightarrow> MemAttrHints" where
  "read_LongConvertAttrsHints attrfield acctype s \<equiv>
     \<lparr>MemAttrHints_attrs =
        if read_S1CacheDisabled acctype s \<or> attrfield = 4 then MemAttr_NC else
        if Word.slice 2 attrfield = (0 :: 2 word) then MemAttr_WT else
        if Word.slice 2 attrfield = (1 :: 2 word) then Word.slice 0 attrfield else
        Word.slice 2 attrfield,
      MemAttrHints_hints =
        if read_S1CacheDisabled acctype s \<or> attrfield = 4 then MemHint_No else
        if Word.slice 2 attrfield = (0 :: 2 word) then Word.slice 0 attrfield else
        if Word.slice 2 attrfield = (1 :: 2 word) then MemAttr_WB else (* Is this intentional? *)
        Word.slice 0 attrfield,
      MemAttrHints_transient =
        if read_S1CacheDisabled acctype s then False else
        attrfield \<noteq> 4 \<and> \<not>(attrfield !! 3)\<rparr>"

definition read_S1AttrDecode :: "2 word \<Rightarrow> 3 word \<Rightarrow> AccType \<Rightarrow> regstate sequential_state \<Rightarrow> MemoryAttributes" where
  "read_S1AttrDecode SH_arg attr acctype s =
     (let mair = read_MAIR (read_S1TranslationRegime (read_EL s) s) s;
          attrslo = Word.slice (nat (8 * uint attr)) mair :: 4 word;
          attrshi = Word.slice (4 + nat (8 * uint attr)) mair :: 4 word;
          ihints = read_LongConvertAttrsHints attrslo acctype s;
          ohints = read_LongConvertAttrsHints attrshi acctype s in
      \<lparr>MemoryAttributes_typ = if attrslo = 0 \<or> attrshi = 0 then MemType_Device else MemType_Normal,
       MemoryAttributes_device =
         if attrslo = 0 \<or> attrshi = 0 then
           (if attrslo = 0 then DeviceType_nGnRnE
            else if attrslo = 4 then DeviceType_nGnRE
            else if attrslo = 8 then DeviceType_nGRE
            else if attrslo = 12 then DeviceType_GRE
            else DeviceType_nGnRnE)
         else DeviceType_GRE,
       MemoryAttributes_inner =
         if attrslo \<noteq> 0 \<and> attrshi \<noteq> 0 then ihints
         else \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = False\<rparr>,
       MemoryAttributes_outer =
         if attrslo \<noteq> 0 \<and> attrshi \<noteq> 0 then ohints
         else \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = False\<rparr>,
       MemoryAttributes_shareable =
         attrslo = 0 \<or> attrshi = 0 \<or>
         MemAttrHints_attrs ihints = 0 \<and> MemAttrHints_attrs ohints = 0 \<or>
         SH_arg !! 1,
       MemoryAttributes_outershareable =
         attrslo = 0 \<or> attrshi = 0 \<or>
         MemAttrHints_attrs ihints = 0 \<and> MemAttrHints_attrs ohints = 0 \<or>
         SH_arg = 2\<rparr>)"

fun read_TTBR0 where
  "read_TTBR0 s =
     (let el = read_S1TranslationRegime (read_EL s) s in
      if el = 3 then TTBR0_EL3 (regstate s) else
      if el = 2 then TTBR0_EL2 (regstate s) else TTBR0_EL1 (regstate s))"

fun read_TTBR1 where
  "read_TTBR1 s =
     (let el = read_S1TranslationRegime (read_EL s) s in
      if el = 3 then TTBR0_EL3 (regstate s) else
      if el = 2 then TTBR1_EL2 (regstate s) else TTBR1_EL1 (regstate s))"

definition read_TTBR :: "bool \<Rightarrow> regstate sequential_state \<Rightarrow> 64 word" where
  "read_TTBR high s = (if high then read_TTBR1 s else read_TTBR0 s)"

definition TTBR_valid_for_vaddr :: "64 word \<Rightarrow> int \<Rightarrow> regstate sequential_state \<Rightarrow> bool" where
  "TTBR_valid_for_vaddr addr addrtop s \<equiv>
     (let high = addr !! nat addrtop;
          p = read_params high s in
        (outputsize p < 48 \<longrightarrow> read_TTBR high s AND slice_mask 64 (outputsize p) (48 - outputsize p) = 0))"

definition addrselecttop :: "int \<Rightarrow> Parameters \<Rightarrow> int" where
  "addrselecttop level p =
     (min (inputsize p) ((4 - level) * (grainsize p - 3) + grainsize p) - 1)"

definition addrselectbottom :: "int \<Rightarrow> Parameters \<Rightarrow> int" where
  "addrselectbottom level p = (3 - level) * (grainsize p - 3) + grainsize p"

definition stride :: "int \<Rightarrow> Parameters \<Rightarrow> int" where
  "stride level p = addrselecttop level p - addrselectbottom level p + 1"

function read_table :: "int \<Rightarrow> bool \<Rightarrow> 52 word \<Rightarrow> regstate sequential_state \<Rightarrow> TableEntry list" where
  "read_table level high baseaddr s =
     (let p = read_params high s;
          stride = stride level p;
          descaddrs = map (\<lambda>idx. baseaddr OR (word_of_int idx << 3)) [0..2 ^ nat stride - 1];
          read_desc =
            (\<lambda>addr. case read_mem_word addr 8 s of
                      None \<Rightarrow> Invalid
                    | Some desc \<Rightarrow>
                        let desc = if read_bigendian s then reverse_endianness desc else desc in
                        (if ValidDescriptor level (grainsize p) (outputsize p) desc \<and> level \<ge> 0 \<and> level < 4 then
                           (if (IsBlockDescriptor desc \<or> level = 3) then Descriptor desc
                            else
                              let lbaseaddr = ((Word.slice (nat (grainsize p)) desc) << nat (grainsize p)) :: 48 word;
                                  ubaseaddr = (if outputsize p = 52 then Word.slice 12 desc else 0) :: 4 word;
                                  baseaddr = word_cat ubaseaddr lbaseaddr :: 52 word;
                                  ns = desc !! 63; ap1 = desc !! 62; ap0 = desc !! 61; xn = desc !! 60; pxn = desc !! 59 in
                              Table baseaddr ns ap1 ap0 xn pxn (read_table (level + 1) high baseaddr s))
                         else Invalid)) in
      map read_desc descaddrs)"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(level, _). 4 - nat level)") auto

lemma size_list_table_nth_dec[termination_simp]:
  assumes i: "i < length table" and table': "table ! i = Table baseaddr ns ap1 ap0 xn pxn table'"
  shows "size_list size table' < size_list size table"
  using table'
  by (auto intro: size_list_estimation[OF nth_mem[OF i]])

fun walk_table :: "64 word \<Rightarrow> int \<Rightarrow> Parameters \<Rightarrow> 52 word \<Rightarrow> TableEntry list \<Rightarrow>
                       (64 word \<times> 52 word \<times> 52 word \<times> int \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool) option" where
  "walk_table inputaddr level p baseaddr table =
     (let index = uint (inputaddr AND slice_mask 52 (addrselectbottom level p) (stride level p) >> nat (addrselectbottom level p));
          descaddr = baseaddr OR (word_of_int index << 3) in
      if nat index < length table then
        (case table ! nat index of
           Invalid \<Rightarrow> None
         | Descriptor desc \<Rightarrow> Some (desc, descaddr, baseaddr, level, False, False, False, False, False)
         | Table baseaddr ns ap1 ap0 xn pxn table \<Rightarrow>
             (case walk_table inputaddr (level + 1) p baseaddr table of
               None \<Rightarrow> None
              | Some (desc, descaddr, baseaddr, level, ns', ap1', ap0', xn', pxn') \<Rightarrow>
                  Some (desc, descaddr, baseaddr, level, ns \<or> ns', ap1 \<or> ap1', ap0 \<or> ap0', xn \<or> xn', pxn \<or> pxn')))
      else None)"

declare walk_table.simps[simp del]

abbreviation
  "default_FaultRecord \<equiv>
     \<lparr>FaultRecord_typ = Fault_None, FaultRecord_acctype = AccType_NORMAL, FaultRecord_ipaddress = 0,
      FaultRecord_s2fs1walk = False, FaultRecord_write = False, FaultRecord_level = 0,
      FaultRecord_extflag = 0, FaultRecord_secondstage = False, FaultRecord_domain = 0,
      FaultRecord_errortype = 0, FaultRecord_debugmoe = 0\<rparr>"

definition valid_perms :: "Permissions \<Rightarrow> AccType \<Rightarrow> bool \<Rightarrow> regstate sequential_state \<Rightarrow> bool" where
  "valid_perms perms acctype iswrite s \<equiv>
     (let wxn = SCTLR_EL1 (regstate s) !! 19;
          r = Permissions_ap perms !! 1;
          w = (Word.slice 1 (Permissions_ap perms) = (1 :: 2 word));
          xn = (Permissions_xn perms = 1) \<or> (w \<and> wxn) in
      if acctype = AccType_IFETCH then \<not>xn
      else if acctype \<in> { AccType_ATOMICRW, AccType_ORDEREDRW } then r \<and> w
      else if iswrite then w
      else r)"

definition lookup_TLBRecord :: "64 word \<Rightarrow> AccType \<Rightarrow> regstate sequential_state \<Rightarrow> TLBRecord option" where
  "lookup_TLBRecord vaddress acctype s =
     (let top = read_AddrTop_EL0 vaddress (acctype = AccType_IFETCH) s;
          high = vaddress !! nat top;
          p = read_params high s;
          baseaddress = baseaddress (read_TTBR high s) (baselowerbound p) (outputsize p);
          hierattrs = \<not>(if high then TCR_EL1 (regstate s) !! 42 else TCR_EL1 (regstate s) !! 41);
          secure = \<not> SCR_EL3 (regstate s) !! 0 in
      case walk_table vaddress (startlevel p) p baseaddress
             (read_table (startlevel p) high baseaddress s) of
        None \<Rightarrow> None
      | Some (desc, descaddr, baseaddr, level, ns, ap1, ap0, xn, pxn) \<Rightarrow>
          let addrselectbottom = addrselectbottom level p;
              walkattrs = read_WalkAttrDecode (SH p) (ORGN p) (IRGN p) False s;
              memattrs = read_S1AttrDecode (Word.slice 8 desc) (Word.slice (Suc (Suc 0)) desc) acctype s;
              perms =
                \<lparr>Permissions_ap = of_bl [\<not>desc !! 51 \<and> desc !! 7 \<or> hierattrs \<and> ap1, desc !! 6 \<and> \<not>(hierattrs \<and> ap0), True],
                 Permissions_xn = of_bl [desc !! 54 \<or> hierattrs \<and> xn],
                 Permissions_xxn = 0,
                 Permissions_pxn = of_bl [desc !! 53 \<or> hierattrs \<and> pxn]\<rparr> in
          if level \<ge> firstblocklevel p \<and>
             valid_vaddr vaddress top s \<and>
             TTBR_valid_for_vaddr vaddress top s \<and>
             (outputsize p < 48 \<longrightarrow>
                desc AND slice_mask 64 (outputsize p) (48 - outputsize p) = 0) \<and>
             (outputsize p < 52 \<and> largegrain p \<longrightarrow> Word.slice 12 desc = (0 :: 4 word)) \<and>
             (contiguousbitcheck p level \<longrightarrow> \<not>desc !! 52)
          then
            let outputaddr :: 52 word =
              if outputsize p = 52
              then word_cat (Word.slice 12 desc :: 4 word)
                     (slice_slice_concat 48 desc addrselectbottom (48 - addrselectbottom)
                                         vaddress 0 addrselectbottom :: 48 word)
              else slice_slice_concat 52 desc addrselectbottom (48 - addrselectbottom) vaddress 0 addrselectbottom in
            Some \<lparr>TLBRecord_perms = perms,
                  TLBRecord_nG = of_bl [desc !! 11 \<or> (secure \<and> ns)],
                  TLBRecord_domain = 0, TLBRecord_contiguous = desc !! 52,
                  TLBRecord_level = level,
                  TLBRecord_blocksize = 2 ^ (nat addrselectbottom),
                  TLBRecord_descupdate =
                    \<lparr>DescriptorUpdate_AF = \<not>desc !! 10,
                     DescriptorUpdate_AP = desc !! 51 \<and> desc !! 7,
                     DescriptorUpdate_descaddr =
                       \<lparr>AddressDescriptor_fault = default_FaultRecord,
                        AddressDescriptor_memattrs = walkattrs,
                        AddressDescriptor_paddress =
                          \<lparr>FullAddress_physicaladdress = descaddr,
                           FullAddress_NS = of_bl [ns \<or> \<not>secure]\<rparr>,
                        AddressDescriptor_vaddress = vaddress\<rparr>\<rparr>,
                  TLBRecord_CnP = of_bl [read_TTBR high s !! 0],
                  TLBRecord_addrdesc =
                    \<lparr>AddressDescriptor_fault = default_FaultRecord,
                     AddressDescriptor_memattrs = memattrs,
                     AddressDescriptor_paddress =
                       \<lparr>FullAddress_physicaladdress = outputaddr,
                        FullAddress_NS = of_bl [desc !! 5 \<or> ns \<or> \<not>secure]\<rparr>,
                     AddressDescriptor_vaddress = vaddress\<rparr> \<rparr>
          else None)"

definition translate_address :: "64 word \<Rightarrow> AccType \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> regstate sequential_state \<Rightarrow> TLBRecord option" where
  "translate_address vaddress acctype iswrite wasaligned s =
     (case lookup_TLBRecord vaddress acctype s of
        None \<Rightarrow> None
      | Some r \<Rightarrow>
          let top = read_AddrTop_EL0 vaddress (acctype = AccType_IFETCH) s in
          if valid_perms (TLBRecord_perms r) acctype iswrite s \<and>
             AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r)) \<noteq> 0x13000000 \<and> (* debug console hard-coded in this ASL model *)
             (MemoryAttributes_typ (AddressDescriptor_memattrs (TLBRecord_addrdesc r)) = MemType_Device \<longrightarrow>
              wasaligned \<and> acctype \<notin> {AccType_IFETCH, AccType_DCZVA})
          then Some r else None)"

definition read_descriptor :: "52 word \<Rightarrow> regstate sequential_state \<Rightarrow> 64 word option" where
  "read_descriptor addr s \<equiv>
     (case read_mem_word addr 8 s of
        None \<Rightarrow> None
      | Some desc \<Rightarrow> Some (if read_bigendian s then reverse_endianness desc else desc))"

definition write_descriptor :: "52 word \<Rightarrow> 64 word \<Rightarrow> regstate sequential_state \<Rightarrow> regstate sequential_state" where
  "write_descriptor addr desc s \<equiv>
     (let desc = if read_bigendian s then reverse_endianness desc else desc in
      write_mem_bytes (uint addr) 8 (mem_bytes_of_word desc) (s\<lparr>write_ea := Some (Write_plain, uint addr, 8)\<rparr>))"

definition update_descriptor :: "DescriptorUpdate \<Rightarrow> AccType \<Rightarrow> bool \<Rightarrow> regstate sequential_state \<Rightarrow> regstate sequential_state" where
  "update_descriptor descupd acctype iswrite s \<equiv>
     (case read_descriptor (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr descupd)) s of
        None \<Rightarrow> s
      | Some desc \<Rightarrow>
          (let ap = DescriptorUpdate_AP descupd \<and>
                    (iswrite \<or> acctype = AccType_ATOMICRW \<or> acctype = AccType_ORDEREDRW) \<and>
                    acctype \<noteq> AccType_AT \<and> acctype \<noteq> AccType_DC;
               af = DescriptorUpdate_AF descupd;
               desc = if af then set_bit desc 10 True else desc;
               desc = if ap then set_bit desc 7 False else desc;
               addr = AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr descupd) in
           if af \<or> ap
           then write_descriptor addr desc s
           else s))"

end
