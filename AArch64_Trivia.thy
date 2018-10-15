theory AArch64_Trivia
  imports "Sail-AArch64.Aarch64_lemmas" Sail.Sail2_operators_mwords_lemmas Word_Extra Proof_methods
begin

text \<open>Various helper lemmas for simplifying proof obligations arising in the computation of
preconditions, e.g. if-then-else-distributivity rules for the datatypes in the model.\<close>

abbreviation
  "CreateFaultRecord typ1 ipaddress level acctype write1 extflag errortype secondstage s2fs1walk \<equiv>
     \<lparr>FaultRecord_typ = typ1, FaultRecord_acctype = acctype, FaultRecord_ipaddress = ipaddress,
      FaultRecord_s2fs1walk = s2fs1walk, FaultRecord_write = write1, FaultRecord_level = level,
      FaultRecord_extflag = extflag, FaultRecord_secondstage = secondstage, FaultRecord_domain = 0,
      FaultRecord_errortype = errortype, FaultRecord_debugmoe = 0\<rparr>"

abbreviation
  "AccessDescriptor acctype ptwalk secondstage s2fs2walk level \<equiv>
     \<lparr>AccessDescriptor_acctype = acctype,
      AccessDescriptor_page_table_walk = ptwalk,
      AccessDescriptor_secondstage = secondstage,
      AccessDescriptor_s2fs1walk = s2fs2walk,
      AccessDescriptor_level = level\<rparr>"

lemma CreateFaultRecord_if_distrib:
  "(if c then CreateFaultRecord typ1 ipaddress1 level1 acctype1 write1 extflag1 errortype1 secondstage1 s2fs1walk1
    else CreateFaultRecord typ2 ipaddress2 level2 acctype2 write2 extflag2 errortype2 secondstage2 s2fs1walk2) =
    CreateFaultRecord (if c then typ1 else typ2) (if c then ipaddress1 else ipaddress2)
      (if c then level1 else level2) (if c then acctype1 else acctype2) (if c then write1 else write2)
      (if c then extflag1 else extflag2) (if c then errortype1 else errortype2)
      (if c then secondstage1 else secondstage2) (if c then s2fs1walk1 else s2fs1walk2)"
  by auto

lemma fun2_if_distrib:
  "(if c then f x1 y1 else f x2 y2) = f (if c then x1 else x2) (if c then y1 else y2)"
  by auto

lemmas fun2_if_distribs =
  if_distrib[where f = f for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c", symmetric]
  fun2_if_distrib
  fun2_if_distrib[where f = Pair]
  fun2_if_distrib[where f = "(\<and>)"]
  fun2_if_distrib[where f = "(\<or>)"]

lemmas prod_if_distrib = fun2_if_distrib[where f = Pair]
lemmas conj_if_distrib = fun2_if_distrib[where f = "(\<and>)"]
lemmas disj_if_distrib = fun2_if_distrib[where f = "(\<or>)"]

lemmas all_if_distrib = if_distrib[where f = "\<lambda>c. \<forall>b. c b", symmetric]

lemmas AddressDescriptor_memattrs_update_if_distrib =
  if_distrib[where f = "\<lambda>c. addrdesc\<lparr>AddressDescriptor_memattrs := c\<rparr>" for addrdesc, symmetric]
  if_distrib[where f = "\<lambda>c. c\<lparr>AddressDescriptor_memattrs := z\<rparr>" for z]

lemma MemoryAttributes_if_distrib:
  "(if c then
      \<lparr>MemoryAttributes_typ = typ1, MemoryAttributes_device = device1,
       MemoryAttributes_inner = inner1, MemoryAttributes_outer = outer1,
       MemoryAttributes_shareable = shareable1, MemoryAttributes_outershareable = outershareable1\<rparr>
    else
      \<lparr>MemoryAttributes_typ = typ2, MemoryAttributes_device = device2,
       MemoryAttributes_inner = inner2, MemoryAttributes_outer = outer2,
       MemoryAttributes_shareable = shareable2, MemoryAttributes_outershareable = outershareable2\<rparr>) =
    \<lparr>MemoryAttributes_typ = if c then typ1 else typ2,
     MemoryAttributes_device = if c then device1 else device2,
     MemoryAttributes_inner = if c then inner1 else inner2,
     MemoryAttributes_outer = if c then outer1 else outer2,
     MemoryAttributes_shareable = if c then shareable1 else shareable2,
     MemoryAttributes_outershareable = if c then outershareable1 else outershareable2\<rparr>"
  by auto

lemma MemoryAttributes_cong:
  assumes "typ1 = typ2" and "device1 = device2" and "inner1 = inner2" and "outer1 = outer2"
    and "shareable1 = shareable2" and "outershareable1 = outershareable2"
  shows
    "\<lparr>MemoryAttributes_typ = typ1, MemoryAttributes_device = device1,
      MemoryAttributes_inner = inner1, MemoryAttributes_outer = outer1,
      MemoryAttributes_shareable = shareable1, MemoryAttributes_outershareable = outershareable1\<rparr> =
     \<lparr>MemoryAttributes_typ = typ2, MemoryAttributes_device = device2,
      MemoryAttributes_inner = inner2, MemoryAttributes_outer = outer2,
      MemoryAttributes_shareable = shareable2, MemoryAttributes_outershareable = outershareable2\<rparr>"
  using assms by auto


lemma MemAttrHints_if_distrib:
  "(if c
    then \<lparr>MemAttrHints_attrs = attrs1, MemAttrHints_hints = hints1, MemAttrHints_transient = transient1\<rparr>
    else \<lparr>MemAttrHints_attrs = attrs2, MemAttrHints_hints = hints2, MemAttrHints_transient = transient2\<rparr>) =
   \<lparr>MemAttrHints_attrs = if c then attrs1 else attrs2,
    MemAttrHints_hints = if c then hints1 else hints2,
    MemAttrHints_transient = if c then transient1 else transient2\<rparr>"
  by auto

lemma MemAttrHints_cong:
  assumes "attrs1 = attrs2" and "hints1 = hints2" and "transient1 = transient2"
  shows "\<lparr>MemAttrHints_attrs = attrs1, MemAttrHints_hints = hints1, MemAttrHints_transient = transient1\<rparr> =
         \<lparr>MemAttrHints_attrs = attrs2, MemAttrHints_hints = hints2, MemAttrHints_transient = transient2\<rparr>"
  using assms by auto

lemma case_option_if_distrib:
  "(if b then (case x1 of Some y \<Rightarrow> f1 y | None \<Rightarrow> g1) else (case x2 of Some y \<Rightarrow> f2 y | None \<Rightarrow> g2)) =
   (case (if b then x1 else x2) of Some y \<Rightarrow> if b then f1 y else f2 y | None \<Rightarrow> if b then g1 else g2)"
  by (auto split: option.splits)

lemma case_prod_if_distrib:
  "(if b then (case x1 of (y1, z1) \<Rightarrow> f1 y1 z1) else (case x2 of (y2, z2) \<Rightarrow> f2 y2 z2)) =
   (case (if b then x1 else x2) of (y, z) \<Rightarrow> if b then f1 y z else f2 y z)"
  by auto

lemma app_let_distrib: "(let x = y in f x) z = (let x = y in f x z)"
  by auto

lemmas TLBRecord_if_distribs[simp] =
  if_distrib[where f = TLBRecord_descupdate] if_distrib[where f = TLBRecord_descupdate_update]
  if_distrib[where f = "\<lambda>x. r\<lparr>TLBRecord_descupdate := x\<rparr>" for r]
  if_distrib[where f = TLBRecord_addrdesc]
lemmas DescriptorUpdate_if_distribs[simp] =
  if_distrib[where f = DescriptorUpdate_descaddr_update]
lemmas MemAttrHints_if_distribs[simp] =
  if_distrib[where f = MemAttrHints_attrs]
lemmas [simp] =
  if_distrib[where f = FullAddress_physicaladdress]
  if_distrib[where f = AddressDescriptor_paddress]
  if_distrib[where f = "\<lambda>i. x < i" for x]
  if_distrib[where f = "\<lambda>i. i < x" for x]
  if_distrib[where f = "\<lambda>i. x - i" for x]
  if_distrib[where f = "\<lambda>i. i = x" for x]

lemmas PrePost_if_distribs = app_if_distrib prod_if_distrib conj_if_distrib disj_if_distrib all_if_distrib
  AddressDescriptor_memattrs_update_if_distrib MemoryAttributes_if_distrib MemAttrHints_if_distrib
  (*TLBRecord_descupdate_update_if_distrib DescriptorUpdate_descaddr_update_if_distrib*)
  if_distrib[where f = "\<lambda>c. z \<le> c" for z] if_distrib[where f = "\<lambda>c. c \<le> z" for z]
  if_distrib[where f = "\<lambda>c. z < c" for z] if_distrib[where f = "\<lambda>c. c < z" for z]
  if_distrib[where f = returnS, symmetric]
  if_distrib[where f = return, symmetric]
  case_option_if_distrib case_prod_if_distrib
  if_distrib[where f = "\<lambda>c. let a = b in c a" for b, symmetric]
  if_distrib[where f = "\<lambda>c. a \<longrightarrow> c" for a, symmetric]
  (*if_distrib[where f = "\<lambda>c. z = c" for z] if_distrib[where f = "\<lambda>c. c = z" for z]*)
  (*if_distrib[where f = "\<lambda>c. c' \<and> c" for c'] if_distrib[where f = "\<lambda>c. c \<and> c'" for c']*)

lemmas app_case_distribs =
  sum.case_distrib[where h = "\<lambda>c. c z" for z]
  ex.case_distrib[where h = "\<lambda>c. c z" for z]
  option.case_distrib[where h = "\<lambda>c. c z" for z]
  app_let_distrib

lemma if_True_False_simps[simp]:
  "(if c then True else False) = c"
  "(if c then False else True) = (\<not>c)"
  "(if c1 then True else c2) = (c1 \<or> c2)"
  "(if c1 then c2 else True) = (c1 \<longrightarrow> c2)"
  "(if c1 then c2 else False) = (c1 \<and> c2)"
  by auto

lemma conj_imp_cond_absorb[simp]: "(b \<longrightarrow> c1) \<and> (b \<longrightarrow> c2) \<longleftrightarrow> (b \<longrightarrow> c1 \<and> c2)"
  by auto

lemma if_then_imp_distrib:
  "(if c then x \<longrightarrow> y else z) = ((c \<and> \<not>x) \<or> (if c then y else z))"
  "(if c then x \<or> y else z) = ((c \<and> x) \<or> (if c then y else z))"
  "(if c then x else y \<longrightarrow> z) = ((\<not>c \<and> \<not>y) \<or> (if c then x else z))"
  "(if c then x else y \<or> z) = ((\<not>c \<and> y) \<or> (if c then x else z))"
  by auto

lemma if_then_all_distrib:
  "\<And>c f g. (if c then \<forall>x. f x else g) = (\<forall>x. if c then f x else g)"
  "\<And>c f g. (if c then f else \<forall>x. g x) = (\<forall>x. if c then f else g x)"
  by auto

lemma if_then_conj_distrib:
  "(if c then x \<and> y else z) = ((c \<longrightarrow> x) \<and> (if c then y else z))"
  "(if c then x else y \<and> z) = ((\<not>c \<longrightarrow> y) \<and> (if c then x else z))"
  by auto

lemma nested_if_merges[simp]:
  "(if c1 then x else if c2 then x else y) = (if c1 \<or> c2 then x else y)"
  "(if c1 then x else if c2 then y else x) = (if c1 \<or> \<not>c2 then x else y)"
  "(if c1 then x else (if c2 then y else (if c3 then x else z))) = (if c1 \<or> (\<not>c2 \<and> c3) then x else if c2 then y else z)"
  "(if c1 then x else (if c2 then (if c3 then x else y) else z)) = (if c1 \<or> (c2 \<and> c3) then x else if c2 then y else z)"
  "(if c1 then (if c2 then x else y) else (if c3 then x else z)) = (if (c1 \<and> c2) \<or> (\<not>c1 \<and> c3) then x else if c1 then y else z)"
  "(if (if a then b else c) then x else y) \<longleftrightarrow> (if (\<not>a \<or> b) \<and> (a \<or> c) then x else y)"
  "(if a then b \<and> c else c) \<longleftrightarrow> (\<not>a \<or> b) \<and> c"
  "(if a then (if b then x else y) else y) \<longleftrightarrow> (if (a \<and> b) then x else y)"
  "(if a then (if b then x else y) else (if c then x else y)) \<longleftrightarrow> (if (\<not>a \<or> b) \<and> (a \<or> c) then x else y)"
  "(\<forall>a. if a \<or> b then x else y) \<longleftrightarrow> x \<and> (if b then x else y)"
  by auto

lemma conj_disj_absorbs[simp]:
  "A \<and> B \<or> A \<longleftrightarrow> A"
  "A \<and> B \<or> B \<longleftrightarrow> B"
  "(A \<and> B) \<or> (\<not>A \<and> B) \<longleftrightarrow> B"
  "(\<not>A \<and> B) \<or> (A \<and> B) \<longleftrightarrow> B"
  by auto

lemma quant_singleton_bool_simps[simp]:
  "(\<forall>b. b) \<longleftrightarrow> False" "(\<forall>b. \<not>b) \<longleftrightarrow> False" "(\<exists>b. b) \<longleftrightarrow> True" "(\<exists>b. \<not>b) \<longleftrightarrow> True"
  by auto

lemmas MemAttr_defs[simp] = MemAttr_WT_def MemAttr_WB_def MemAttr_NC_def

lemma case_prod15_split:
  "(case vars of (accdesc, addrselectbottom, addrselecttop, ap_table, baseaddress, blocktranslate, desc, descaddr, descaddr2, hwupdatewalk, level,
                     ns_table, pxn_table, result, xn_table) \<Rightarrow>
      f accdesc addrselectbottom addrselecttop ap_table baseaddress blocktranslate desc descaddr descaddr2 hwupdatewalk level
                     ns_table pxn_table result xn_table) =
   (\<forall>accdesc addrselectbottom addrselecttop ap_table baseaddress blocktranslate desc descaddr descaddr2 hwupdatewalk level
                     ns_table pxn_table result xn_table.
      vars = (accdesc, addrselectbottom, addrselecttop, ap_table, baseaddress, blocktranslate, desc, descaddr, descaddr2, hwupdatewalk, level,
                     ns_table, pxn_table, result, xn_table) \<longrightarrow>
      f accdesc addrselectbottom addrselecttop ap_table baseaddress blocktranslate desc descaddr descaddr2 hwupdatewalk level
                     ns_table pxn_table result xn_table)"
  by auto

lemma prod15_cases:
  obtains accdesc addrselectbottom addrselecttop ap_table baseaddress blocktranslate desc descaddr descaddr2 hwupdatewalk level
                     ns_table pxn_table result xn_table
                   where "x = (accdesc, addrselectbottom, addrselecttop, ap_table, baseaddress, blocktranslate, desc, descaddr, descaddr2, hwupdatewalk, level,
                     ns_table, pxn_table, result, xn_table)"
  by (cases x) auto

lemma TLBRecord_if_distrib:
  "(if c then
      \<lparr>TLBRecord_perms =
         \<lparr>Permissions_ap = ap1, Permissions_xn = xn1, Permissions_xxn = xxn1, Permissions_pxn = pxn1\<rparr>,
       TLBRecord_nG = nG1, TLBRecord_domain = domain1, TLBRecord_contiguous = contiguous1,
       TLBRecord_level = level1, TLBRecord_blocksize = blocksize1,
       TLBRecord_descupdate =
         \<lparr>DescriptorUpdate_AF = af1, DescriptorUpdate_AP = descupd_ap1,
          DescriptorUpdate_descaddr = descaddr1 \<rparr>,
       TLBRecord_CnP = cnp1,
       TLBRecord_addrdesc =
         \<lparr>AddressDescriptor_fault = fault1, AddressDescriptor_memattrs = memattrs1,
          AddressDescriptor_paddress = \<lparr>FullAddress_physicaladdress = paddress1, FullAddress_NS = ns1\<rparr>,
          AddressDescriptor_vaddress = vaddress1\<rparr> \<rparr>
    else
      \<lparr>TLBRecord_perms =
         \<lparr>Permissions_ap = ap2, Permissions_xn = xn2, Permissions_xxn = xxn2, Permissions_pxn = pxn2\<rparr>,
       TLBRecord_nG = nG2, TLBRecord_domain = domain2, TLBRecord_contiguous = contiguous2,
       TLBRecord_level = level2, TLBRecord_blocksize = blocksize2,
       TLBRecord_descupdate =
         \<lparr>DescriptorUpdate_AF = af2, DescriptorUpdate_AP = descupd_ap2, DescriptorUpdate_descaddr = descaddr2 \<rparr>,
       TLBRecord_CnP = cnp2,
       TLBRecord_addrdesc =
         \<lparr>AddressDescriptor_fault = fault2, AddressDescriptor_memattrs = memattrs2,
          AddressDescriptor_paddress = \<lparr>FullAddress_physicaladdress = paddress2, FullAddress_NS = ns2\<rparr>,
          AddressDescriptor_vaddress = vaddress2\<rparr> \<rparr>) =
       \<lparr>TLBRecord_perms =
          \<lparr>Permissions_ap = if c then ap1 else ap2,
           Permissions_xn = if c then xn1 else xn2,
           Permissions_xxn = if c then xxn1 else xxn2,
           Permissions_pxn = if c then pxn1 else pxn2\<rparr>,
        TLBRecord_nG = if c then nG1 else nG2,
        TLBRecord_domain = if c then domain1 else domain2,
        TLBRecord_contiguous = if c then contiguous1 else contiguous2,
        TLBRecord_level = if c then level1 else level2,
        TLBRecord_blocksize = if c then blocksize1 else blocksize2,
        TLBRecord_descupdate =
          \<lparr>DescriptorUpdate_AF = if c then af1 else af2,
           DescriptorUpdate_AP = if c then descupd_ap1 else descupd_ap2,
           DescriptorUpdate_descaddr = if c then descaddr1 else descaddr2 \<rparr>,
        TLBRecord_CnP = if c then cnp1 else cnp2,
        TLBRecord_addrdesc =
          \<lparr>AddressDescriptor_fault = if c then fault1 else fault2,
           AddressDescriptor_memattrs = if c then memattrs1 else memattrs2,
           AddressDescriptor_paddress =
              \<lparr>FullAddress_physicaladdress = if c then paddress1 else paddress2,
               FullAddress_NS = if c then ns1 else ns2\<rparr>,
           AddressDescriptor_vaddress = if c then vaddress1 else vaddress2\<rparr> \<rparr>"
  by auto

lemma DescriptorUpdate_if_distrib:
  "(if c
    then \<lparr>DescriptorUpdate_AF = af1, DescriptorUpdate_AP = ap1, DescriptorUpdate_descaddr = addr1\<rparr>
    else \<lparr>DescriptorUpdate_AF = af2, DescriptorUpdate_AP = ap2, DescriptorUpdate_descaddr = addr2\<rparr>) =
   \<lparr>DescriptorUpdate_AF = if c then af1 else af2,
    DescriptorUpdate_AP = if c then ap1 else ap2,
    DescriptorUpdate_descaddr = if c then addr1 else addr2\<rparr>"
  by auto


(* Add some lemmas for automatically splitting TLBRecords into their components during precondition
   computation.  This seems to make simplification of record updates more efficient. *)

lemma TLBRecord_cases:
  fixes x :: TLBRecord
  obtains ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap descaddr cnp fault memattrs paddress ns vaddress
  where "x = \<lparr>TLBRecord_perms =
                \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn, Permissions_pxn = pxn\<rparr>,
              TLBRecord_nG = nG, TLBRecord_domain = domain, TLBRecord_contiguous = contiguous,
              TLBRecord_level = level, TLBRecord_blocksize = blocksize,
              TLBRecord_descupdate =
                \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                 DescriptorUpdate_descaddr = descaddr \<rparr>,
              TLBRecord_CnP = cnp,
              TLBRecord_addrdesc =
                \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                 AddressDescriptor_paddress = \<lparr>FullAddress_physicaladdress = paddress, FullAddress_NS = ns\<rparr>,
                 AddressDescriptor_vaddress = vaddress\<rparr> \<rparr>"
proof -
  obtain perms nG domain contiguous level blocksize descupdate cnp addrdesc where
    "x = \<lparr>TLBRecord_perms = perms, TLBRecord_nG = nG, TLBRecord_domain = domain,
          TLBRecord_contiguous = contiguous, TLBRecord_level = level,
          TLBRecord_blocksize = blocksize, TLBRecord_descupdate = descupdate,
          TLBRecord_CnP = cnp, TLBRecord_addrdesc = addrdesc \<rparr>"
    by (cases x)
  moreover obtain ap xn xxn pxn where
    "perms = \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn, Permissions_pxn = pxn\<rparr>"
    by (cases perms)
  moreover obtain af descupd_ap descaddr where
    "descupdate = \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                   DescriptorUpdate_descaddr = descaddr \<rparr>"
    by (cases descupdate)
  moreover obtain fault memattrs paddress' vaddress where
    "addrdesc = \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                  AddressDescriptor_paddress = paddress', AddressDescriptor_vaddress = vaddress\<rparr>"
    by (cases addrdesc)
  moreover obtain paddress ns where
    "paddress' = \<lparr>FullAddress_physicaladdress = paddress, FullAddress_NS = ns\<rparr>"
    by (cases paddress')
  ultimately show thesis using that by blast
qed

lemma PrePostE_bindS_TLBRecord:
  assumes f:
    "\<And>ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap descaddr cnp fault memattrs paddress ns vaddress.
        PrePostE (P' ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap descaddr
                     cnp fault memattrs paddress ns vaddress)
                 (f (\<lparr>TLBRecord_perms =
                        \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn, Permissions_pxn = pxn\<rparr>,
                      TLBRecord_nG = nG, TLBRecord_domain = domain, TLBRecord_contiguous = contiguous,
                      TLBRecord_level = level, TLBRecord_blocksize = blocksize,
                      TLBRecord_descupdate =
                        \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                         DescriptorUpdate_descaddr = descaddr \<rparr>,
                      TLBRecord_CnP = cnp,
                      TLBRecord_addrdesc =
                        \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                         AddressDescriptor_paddress =
                            \<lparr>FullAddress_physicaladdress = paddress,
                             FullAddress_NS = ns\<rparr>,
                         AddressDescriptor_vaddress = vaddress\<rparr> \<rparr>)) Q E"
    and m: "PrePostE P m
                     (\<lambda>r s. \<forall>ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap descaddr
                             cnp fault memattrs paddress ns vaddress.
                          \<lparr>TLBRecord_perms =
                             \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn, Permissions_pxn = pxn\<rparr>,
                           TLBRecord_nG = nG, TLBRecord_domain = domain, TLBRecord_contiguous = contiguous,
                           TLBRecord_level = level, TLBRecord_blocksize = blocksize,
                           TLBRecord_descupdate =
                             \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                              DescriptorUpdate_descaddr = descaddr \<rparr>,
                           TLBRecord_CnP = cnp,
                           TLBRecord_addrdesc =
                             \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                              AddressDescriptor_paddress =
                                 \<lparr>FullAddress_physicaladdress = paddress,
                                  FullAddress_NS = ns\<rparr>,
                              AddressDescriptor_vaddress = vaddress\<rparr> \<rparr> = r \<longrightarrow>
                          P' ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap descaddr
                             cnp fault memattrs paddress ns vaddress s) E"
        (is "PrePostE P m ?R E")
  shows "PrePostE P (bindS m f) Q E"
proof (intro PrePostE_bindS_any)
  fix a
  show "PrePostE (?R a) (f a) Q E"
    by (cases a rule: TLBRecord_cases) (auto intro: f)
  show "PrePostE P m ?R E" using m .
qed

lemma PrePostE_bindS_prod15_TLBRecord14:
  assumes
    "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 ap xn xxn pxn nG domain contiguous level
      blocksize af descupd_ap descaddr cnp fault memattrs paddress ns vaddress.
       PrePostE (P' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ap xn xxn pxn nG domain contiguous level
                    blocksize af descupd_ap descaddr cnp fault memattrs paddress ns vaddress x15)
                (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13,
                    \<lparr>TLBRecord_perms =
                      \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn, Permissions_pxn = pxn\<rparr>,
                     TLBRecord_nG = nG, TLBRecord_domain = domain, TLBRecord_contiguous = contiguous,
                     TLBRecord_level = level, TLBRecord_blocksize = blocksize,
                     TLBRecord_descupdate =
                       \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                        DescriptorUpdate_descaddr = descaddr \<rparr>,
                     TLBRecord_CnP = cnp,
                     TLBRecord_addrdesc =
                       \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                        AddressDescriptor_paddress =
                           \<lparr>FullAddress_physicaladdress = paddress, FullAddress_NS = ns\<rparr>,
                        AddressDescriptor_vaddress = vaddress\<rparr> \<rparr>, x15)) Q E"
    and "PrePostE P m
                  (\<lambda>r s. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) \<Rightarrow>
                         (\<forall>ap xn xxn pxn nG domain contiguous level blocksize af descupd_ap
                           descaddr cnp fault memattrs paddress ns vaddress.
                         (\<lparr>TLBRecord_perms =
                             \<lparr>Permissions_ap = ap, Permissions_xn = xn, Permissions_xxn = xxn,
                              Permissions_pxn = pxn\<rparr>,
                           TLBRecord_nG = nG, TLBRecord_domain = domain, TLBRecord_contiguous = contiguous,
                           TLBRecord_level = level, TLBRecord_blocksize = blocksize,
                           TLBRecord_descupdate =
                             \<lparr>DescriptorUpdate_AF = af, DescriptorUpdate_AP = descupd_ap,
                              DescriptorUpdate_descaddr = descaddr \<rparr>,
                           TLBRecord_CnP = cnp,
                           TLBRecord_addrdesc =
                             \<lparr>AddressDescriptor_fault = fault, AddressDescriptor_memattrs = memattrs,
                              AddressDescriptor_paddress =
                                 \<lparr>FullAddress_physicaladdress = paddress, FullAddress_NS = ns\<rparr>,
                              AddressDescriptor_vaddress = vaddress\<rparr> \<rparr>) = x14 \<longrightarrow>
                          P' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ap xn xxn pxn nG domain
                             contiguous level blocksize af descupd_ap descaddr cnp fault memattrs
                             paddress ns vaddress x15 s)) E"
    (is "PrePostE P m ?R E")
  shows "PrePostE P (bindS m f) Q E"
proof (intro PrePostE_bindS_any)
  fix a :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<times> 'g \<times> 'h \<times> 'i \<times> 'j \<times> 'k \<times> 'l \<times> 'm \<times> TLBRecord \<times> 'n"
  obtain x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    where "a = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15)"
    by (cases a rule: prod15_cases)
  then show "PrePostE (?R a) (f a) Q E"
    by (cases x14 rule: TLBRecord_cases) (auto intro: assms)
  show "PrePostE P m ?R E" using assms(2) .
qed

lemmas PrePostE_bindS_TLBRecords = PrePostE_bindS_TLBRecord PrePostE_bindS_prod15_TLBRecord14

lemma option_case_prod_9_None_False_elim:
  assumes "case x of None \<Rightarrow> False
             | Some (x1, x2, x3, x4, x5, x6, x7, x8, x9) \<Rightarrow> P x1 x2 x3 x4 x5 x6 x7 x8 x9"
  obtains x1 x2 x3 x4 x5 x6 x7 x8 x9
  where "Some (x1, x2, x3, x4, x5, x6, x7, x8, x9) = x"
    and "P x1 x2 x3 x4 x5 x6 x7 x8 x9"
  using assms by (cases x) auto

lemma GetSlice_int_get_slice_int[simp]:
  "GetSlice_int (len :: 'a::len itself) n i = get_slice_int (int LENGTH('a)) n i"
  by (auto simp: GetSlice_int_def)

lemmas [simp] = ex_int_def ex_nat_def

declare extzv_def[simp]

lemma slice_mask_mask: "slice_mask outlen i l = (mask (nat l)) << (nat i)"
  by (auto simp: slice_mask_def mask_def)

lemma HasArchVersion_True: "HasArchVersion v = True"
  by (cases v; auto simp: HasArchVersion_def)

lemma HaveEL_True: "HaveEL el = True"
  by (auto simp: HaveEL_def)

lemmas Have_simps[simp] = HaveEL_True HasArchVersion_True Have52BitPAExt_def Have52BitVAExt_def
  HaveAccessFlagUpdateExt_def HaveAtomicExt_def HaveCommonNotPrivateTransExt_def
  HaveDirtyBitModifierExt_def HaveExtendedExecuteNeverExt_def HaveFJCVTZSExt_def HaveNVExt_def
  HavePACExt_def HavePANExt_def HavePrivATExt_def HaveStatisticalProfiling_def
  HaveTrapLoadStoreMultipleDeviceExt_def HaveUAOExt_def HaveVirtHostExt_def HaveRASExt_def
  HaveCRCExt_def AArch64_HaveHPDExt_def

lemma PAMax_simp: "PAMax () = 52" by (auto simp: PAMax_def IMPDEF_integer_def)

lemma Zeros__0_0[simp]: "Zeros__0 n = 0" by (auto simp: Zeros__0_def)
lemma IsZero_iff_eq0[simp]: "IsZero w \<longleftrightarrow> w = 0" by (auto simp: IsZero_def Zeros__0_def)

lemma ZeroExtend_simps[simp]:
  "\<And>N w. LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> ZeroExtend__0 w N = return (ucast (w :: 'a::len word) :: 'b::len word)"
  "\<And>N w. LENGTH('c) \<le> LENGTH('d) \<Longrightarrow> ZeroExtend__1 N w = return (ucast (w :: 'c::len word) :: 'd::len word)"
  by (auto simp: ZeroExtend__1_def ZeroExtend__0_def)

lemma ZeroExtend__1_64_64_return: "ZeroExtend__1 64 (w :: 64 word) = return w"
  by auto

lemma undefined_bitvector_simp[simp]: "undefined_bitvector n = return 0"
  by (auto simp add: undefined_bitvector_def simp del: repeat.simps)

lemma hex_slice_13000000[simp]: "hex_slice ''0x13000000'' 52 0 = return (0x13000000 :: 52 word)"
  by (auto simp: hex_slice_def hexstring_to_bools_def hexchar_to_bool_list_def ext_list_def maybe_fail_def
                 subrange_list_def subrange_list_dec_def subrange_list_inc_def split_at_def)

definition aligned :: "'n::len word \<Rightarrow> int \<Rightarrow> bool" where
  "aligned w n \<equiv> n dvd uint w"

lemma aligned_8_mask_3: "aligned w 8 \<longleftrightarrow> (w AND mask 3) = 0"
  using and_mask_dvd[where n = 3]
  by (auto simp: aligned_def)

lemma aligned8_OR_distrib: "aligned (x OR y) 8 \<longleftrightarrow> aligned x 8 \<and> aligned y 8"
  by (auto simp: aligned_8_mask_3 word_bool_alg.conj_disj_distrib2)

lemma aligned8_ucast:
  fixes a :: "'a::len word"
  defines "b \<equiv> ucast a :: 'b::len word"
  assumes b: "3 \<le> LENGTH('b)"
  shows "aligned b 8 \<longleftrightarrow> aligned a 8"
  using b test_bit_size[of b] unfolding b_def
  by (auto simp: aligned_8_mask_3 word_and_mask_0_iff_not_testbits nth_ucast)

lemma aligned8_shiftl_3: "i \<ge> 3 \<Longrightarrow> aligned (x << i) 8"
  by (auto simp: aligned_8_mask_3 word_and_mask_0_iff_not_testbits nth_shiftl)

lemma aligned8_word_cat:
  fixes a :: "'a::len word" and b :: "'b::len word"
  defines "c \<equiv> word_cat a b :: 'c::len word"
  assumes b: "3 \<le> LENGTH('b)" and c: "LENGTH('b) \<le> LENGTH('c)"
  shows "aligned c 8 \<longleftrightarrow> aligned b 8"
  using b c unfolding c_def
  by (auto simp: word_cat_shiftl_OR aligned8_OR_distrib aligned8_shiftl_3 aligned8_ucast)

lemma slice_zeros_concat_slice_and_mask[simp]:
  fixes xs :: "'a::len word"
  shows "slice_zeros_concat outlen xs i l l' = (Word.slice (nat i) xs AND mask (nat l)) << nat l'"
proof -
  have "n - nat l' < LENGTH('a) \<and> n + nat i - nat l' < LENGTH('a)"
    if "xs !! (n + nat i - nat l')" for n
    using that by (auto dest: test_bit_size[of xs])
  then show ?thesis
    unfolding slice_zeros_concat_def slice_mask_mask
    by (intro word_eqI) (auto simp: ucast_shiftr word_ao_nth nth_shiftl nth_slice)
qed

lemmas aligned8_simps = aligned8_OR_distrib aligned8_shiftl_3 aligned8_word_cat aligned8_ucast

lemma place_slice_grainsize:
  assumes "grainsize \<ge> 0"
  shows "(place_slice 52 (w :: 64 word) grainsize (48 - grainsize) grainsize :: 52 word) =
         word_cat (0 :: 4 word) ((Word.slice (nat grainsize) w << nat grainsize) :: 48 word)"
  using assms
  by (intro word_eqI)
     (auto simp: place_slice_def slice_mask_mask nth_shiftl nth_shiftr nth_slice word_ao_nth nth_ucast)

lemma set_slice_of_bl_drop_take:
  fixes out :: "'a::len word" and bs :: "bool list"
  (*defines "v \<equiv> of_bl bs :: 'b::len word"*)
  assumes "n \<ge> 0" and "slice_len > 0" and "n + slice_len \<le> int LENGTH('a)" (*and "length bs = LENGTH('b)"*)
  shows "set_slice out_len slice_len (out :: 'a::len word) n v =
           of_bl (take (LENGTH('a) - nat n - nat slice_len) (to_bl out) @
                  to_bl v @
                  drop (LENGTH('a) - nat n) (to_bl out))"
  using assms unfolding set_slice_def
  by (auto simp: update_subrange_vec_dec_update_subrange_list_dec update_subrange_list_dec_drop_take nat_add_distrib)

lemma NOT_of_bl[simp]:
  fixes bs :: "bool list"
  defines "w \<equiv> of_bl bs :: 'a::len word"
  assumes "length bs = LENGTH('a)"
  shows "NOT w = of_bl (map Not bs)"
  using assms by (intro word_eqI) (auto simp: word_ops_nth_size test_bit_of_bl rev_map)

lemma of_bl_AND_of_bl:
  assumes "length l = length r"
  shows "(of_bl l) AND (of_bl r) = of_bl (map2 (\<and>) l r)"
  using assms
  by (intro word_eqI) (auto simp: word_ops_nth_size test_bit_of_bl map2_def rev_map zip_rev[symmetric])

lemma True_OR_1word_absorb: "1 OR (w :: 1 word) = 1"
  by (intro word_eqI) (auto simp: word_ao_nth)

lemma to_bl_1_1word: "to_bl (1 :: 1 word) = [True]"
  by eval

lemma of_bl_test_bit_1word[simp]: "of_bl [w !! 0] = (w :: 1 word)"
  by (intro word_eqI) (auto simp: test_bit_of_bl)

lemma all_bool_neq_or_iff: "(\<forall>b. x = (\<not>b) \<or> P b) = P x"
  by (cases x) (auto simp: all_bool_eq)

lemma arg_cong5:
  assumes "a = a'" and "b = b'" and "c = c'" and "d = d'" and "e = e'"
  shows "f a b c d e = f a' b' c' d' e'"
  using assms by auto

lemma Suc_Suc_0_eq_2: "Suc (Suc 0) = 2"
  by auto

lemma nth_rev_drop: "i < length xs - n \<Longrightarrow> rev (drop n xs) ! i = rev xs ! i"
  by (auto simp: rev_drop)

lemma nth_rev_to_bl:
  fixes w :: "'a::len word"
  assumes "i < LENGTH('a)"
  shows "rev (to_bl w) ! i = w !! i"
  using assms by (auto simp: test_bit_bl)

lemma Let_const[simp]: "(let x = y in f) = f"
  by auto

lemma word_slice_if_distrib: "(Word.slice n (if c then x else y) = z) \<longleftrightarrow> (if c then Word.slice n x = z else Word.slice n y = z)"
  by auto

lemma [simp]: "(if c then False else x) \<longleftrightarrow> (\<not>c \<and> x)"
  by auto

lemma word4_and3_exhaust:
  fixes x :: "4 word"
  shows "x AND 3 = 0 \<longrightarrow> x = 0 \<or> x = 4 \<or> x = 8 \<or> x = 12"
  by (cases x rule: exhaustive_4_word) auto

lemma word4_and3_exhaust':
  fixes x :: "4 word"
  assumes "x AND 3 = 0" and "x \<noteq> 0" and "x \<noteq> 4" and "x \<noteq> 8"
  shows "x = 12"
  using assms by (cases x rule: exhaustive_4_word) auto

lemma [simp]:
  "bitU_of_bool b = B0 \<longleftrightarrow> \<not>b"
  "bitU_of_bool b = B1 \<longleftrightarrow> b"
  by (auto simp: bitU_of_bool_def)

lemma word1_OR_of_bl_disj[simp]:
  fixes w :: "1 word"
  shows "w OR of_bl [b] = of_bl [w !! 0 \<or> b]" and "of_bl [b] OR w = of_bl [b \<or> w !! 0]"
  by (intro word_eqI; auto simp: word_ao_nth test_bit_of_bl)+

lemma nat_lt_2_cases:
  fixes n :: nat
  assumes "n < 2" and "P 0" and "P 1"
  shows "P n"
  using assms by (cases n) auto

lemma word2_OR_of_bl_disj[simp]:
  fixes w :: "2 word"
  shows "w OR of_bl [b1, b0] = of_bl [w !! 1 \<or> b1, w !! 0 \<or> b0]"
    and "of_bl [b1, b0] OR w = of_bl [b1 \<or> w !! 1, b0 \<or> w !! 0]"
  by (intro word_eqI; auto elim!: nat_lt_2_cases simp: word_ao_nth test_bit_of_bl)+

lemma word2_of_bl_test_bits_eq[simp]:
  "of_bl [w !! Suc 0, w !! 0] = (w :: 2 word)"
  by (intro word_eqI; auto elim!: nat_lt_2_cases simp: test_bit_of_bl)

lemma set_slice_2_1_of_bl[simp]:
  "set_slice 2 1 (out :: 2 word) 1 (v :: 1 word) = of_bl [v !! 0, out !! 0]"
  "set_slice 2 1 (out :: 2 word) 0 (v :: 1 word) = of_bl [out !! 1, v !! 0]"
  by (intro word_eqI;
      auto simp: set_slice_def update_subrange_vec_dec_update_subrange_list_dec
                 update_subrange_list_dec_drop_take test_bit_of_bl nth_rev nth_append to_bl_nth
                 elim!: nat_lt_2_cases)+

lemma case_prod_elims:
  "\<And>Q P z thesis. Q (case z of (a, b, c, d, e, f, g) \<Rightarrow> P a b c d e f g) \<Longrightarrow> (\<And>a b c d e f g. z = (a, b, c, d, e, f, g) \<Longrightarrow> Q (P a b c d e f g) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  "\<And>Q P z thesis. Q (case z of (a, b, c, d, e, f) \<Rightarrow> P a b c d e f) \<Longrightarrow> (\<And>a b c d e f. z = (a, b, c, d, e, f) \<Longrightarrow> Q (P a b c d e f) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  "\<And>Q P z thesis. Q (case z of (a, b, c, d, e) \<Rightarrow> P a b c d e) \<Longrightarrow> (\<And>a b c d e. z = (a, b, c, d, e) \<Longrightarrow> Q (P a b c d e) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  "\<And>Q P z thesis. Q (case z of (a, b, c, d) \<Rightarrow> P a b c d) \<Longrightarrow> (\<And>a b c d. z = (a, b, c, d) \<Longrightarrow> Q (P a b c d) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  "\<And>Q P z thesis. Q (case z of (a, b, c) \<Rightarrow> P a b c) \<Longrightarrow> (\<And>a b c. z = (a, b, c) \<Longrightarrow> Q (P a b c) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  "\<And>Q P z thesis. Q (case z of (a, b) \<Rightarrow> P a b) \<Longrightarrow> (\<And>a b. z = (a, b) \<Longrightarrow> Q (P a b) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by auto

lemmas Run_case_prodE = case_prod_elims[where Q = "\<lambda>c. Run c t a" for t a]

lemma set_slice_set_bit[simp]:
  assumes "nat i < LENGTH('a)"
  shows "set_slice len 1 (w :: 'a::len word) i (b :: 1 word) = set_bit w (nat i) (b !! 0)"
  using assms
  by (intro word_eqI)
     (auto simp: set_slice_def test_bit_set_gen update_subrange_vec_dec_def
                word_update_def Let_def test_bit_of_bl nth_append nth_rev to_bl_nth)

lemma slice_set_bit_below:
  shows "m > n \<Longrightarrow> Word.slice m (set_bit w n x) = Word.slice m w"
  by (intro word_eqI) (auto simp: nth_slice test_bit_set_gen)

lemma slice_set_bit_above:
  fixes w :: "'a::len word" and m :: nat
  defines "w' \<equiv> Word.slice m w :: 'b::len word"
  assumes "m + LENGTH('b) < n"
  shows "Word.slice m (set_bit w n x) = w'"
  using assms by (intro word_eqI) (auto simp: nth_slice test_bit_set_gen)

lemma set_bit_3_word:
  fixes w :: "3 word"
  shows "set_bit w 0 x = of_bl [w !! 2, w !! (Suc 0), x]"
        "set_bit w (Suc 0) x = of_bl [w !! 2, x, w !! 0]"
        "set_bit w 2 x = of_bl [x, w !! (Suc 0), w !! 0]"
  by (cases w rule: exhaustive_3_word; cases x; auto)+

lemma case_None_False_exists_Some:
  "(case x of None \<Rightarrow> False | Some y \<Rightarrow> P y) \<longleftrightarrow> (\<exists>y. Some y = x \<and> P y)"
  by (auto split: option.splits)

lemma case_None_Not_exists_Some:
  "\<not>P f1 \<Longrightarrow> (P (case x of None \<Rightarrow> f1 | Some y \<Rightarrow> f2 y)) = (\<exists>y. Some y = x \<and> P (f2 y))"
  by (auto split: option.splits)

lemma Some_eq_if_Some_None_iff_eq:
  "(Some x = (if c then Some y else None)) \<longleftrightarrow> (c \<and> x = y)"
  by auto

lemma Align__1_8_iff_aligned_8[simp]: "(w = Align__1 w 8) \<longleftrightarrow> aligned (w :: 52 word) 8"
proof
  assume "w = Align__1 w 8"
  then have w: "w = word_of_int (8 * (uint w div 8))"
    by (auto simp: Align__1_def Align__0_def of_bl_bin_word_of_int)
  have 8: "(8 :: int) dvd 2 ^ 52" by eval
  show "aligned w 8"
    using dvd_mod_iff[OF 8]
    by (subst w) (auto simp: aligned_def uint_word_of_int)
next
  assume "aligned w 8"
  then show "w = Align__1 w 8"
    by (auto simp: Align__1_def Align__0_def aligned_def of_bl_bin_word_of_int)
qed

end
