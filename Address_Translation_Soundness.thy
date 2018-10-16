(*<*)
(* Author: Thomas Bauereiss *)
theory Address_Translation_Soundness
  imports Address_Translation_Pure
begin
(*>*)

section \<open>Soundness of pure characterisation\<close>

subsection \<open>Assumptions on system register state\<close>

abbreviation
  "InUserMode s \<equiv>
     read_EL s = 0 \<and>           (* Exception level 0 *)
     SCR_EL3 (regstate s) !! 0 (* Non-Secure Mode *)"

abbreviation
  "MMUEnabled_EL01 s \<equiv>
     SCTLR_EL1 (regstate s) !! 0 \<and>  (* MMU enabled *)
     \<not> TCR_EL1 (regstate s) !! 7 \<and>  (* First stage translation enabled (low) *)
     \<not> TCR_EL1 (regstate s) !! 23 \<and> (* First stage translation enabled (high) *)
     \<not> HCR_EL2 (regstate s) !! 27   (* Trap General Exceptions disabled;
                                       would implicitly disable MMU in Non-Secure EL0 *)"

abbreviation
  "VirtDisabled s \<equiv>
     \<not> HCR_EL2 (regstate s) !! 0 \<and>  \<not> HCR_EL2 (regstate s) !! 12 \<and> (* Virtualisation disabled *)
     \<not> HCR_EL2 (regstate s) !! 42 \<and> \<not> HCR_EL2 (regstate s) !! 43 (* Nested virtualisation disabled *)"

abbreviation
  "HwUpdatesFlags s \<equiv>
     TCR_EL1 (regstate s) !! 39 \<and> (* hardware update of access flag *)
     TCR_EL1 (regstate s) !! 40   (* hardware update of dirty bit *)"

abbreviation "DebugDisabled s \<equiv> DBGEN (regstate s) = LOW \<and> \<not>MDSCR_EL1 (regstate s) !! 15"

subsection \<open>Equivalence relations for partially nondeterministic results\<close>

text \<open>Some parts of the results returned by the original translation functions are UNKNOWN,
e.g. the device type field for non-device memory or fault attributes when no fault occurred.
In the Sail model, this is mapped to a nondeterministic choice of unknown fields.  Our pure
characterisation of address translation only captures the deterministic parts.  The following
equivalence relations require equality of those deterministic parts and ignore nondeterministic
fields.\<close>

definition det_equiv_MemAttrHints :: "MemAttrHints \<Rightarrow> MemAttrHints \<Rightarrow> bool" where
  "det_equiv_MemAttrHints l r \<equiv>
     MemAttrHints_attrs l = MemAttrHints_attrs r \<and>
     MemAttrHints_hints l = MemAttrHints_hints r"

definition det_equiv_MemoryAttributes :: "MemoryAttributes \<Rightarrow> MemoryAttributes \<Rightarrow> bool" where
  "det_equiv_MemoryAttributes l r \<equiv>
     MemoryAttributes_typ l = MemoryAttributes_typ r \<and>
     (*MemoryAttributes_device l = MemoryAttributes_device r \<and>*)
     det_equiv_MemAttrHints (MemoryAttributes_inner l) (MemoryAttributes_inner r) \<and>
     det_equiv_MemAttrHints (MemoryAttributes_outer l) (MemoryAttributes_outer r) \<and>
     MemoryAttributes_shareable l = MemoryAttributes_shareable r \<and>
     MemoryAttributes_outershareable l = MemoryAttributes_outershareable r"

definition det_equiv_Permissions :: "Permissions \<Rightarrow> Permissions \<Rightarrow> bool" where
  "det_equiv_Permissions l r \<equiv>
     Permissions_ap l = Permissions_ap r \<and>
     Permissions_xn l = Permissions_xn r \<and>
     Permissions_pxn l = Permissions_pxn r"

definition det_equiv_Fault :: "FaultRecord \<Rightarrow> FaultRecord \<Rightarrow> bool" where
  "det_equiv_Fault l r \<equiv> FaultRecord_typ l = FaultRecord_typ r"

definition det_equiv_AddressDescriptor :: "AddressDescriptor \<Rightarrow> AddressDescriptor \<Rightarrow> bool" where
  "det_equiv_AddressDescriptor l r \<equiv>
     det_equiv_Fault (AddressDescriptor_fault l) (AddressDescriptor_fault r) \<and>
     det_equiv_MemoryAttributes (AddressDescriptor_memattrs l) (AddressDescriptor_memattrs r) \<and>
     AddressDescriptor_paddress l = AddressDescriptor_paddress r"

definition det_equiv_DescriptorUpdate :: "DescriptorUpdate \<Rightarrow> DescriptorUpdate \<Rightarrow> bool" where
  "det_equiv_DescriptorUpdate l r \<equiv>
     DescriptorUpdate_AF l = DescriptorUpdate_AF r \<and>
     DescriptorUpdate_AP l = DescriptorUpdate_AP r \<and>
     det_equiv_AddressDescriptor (DescriptorUpdate_descaddr l) (DescriptorUpdate_descaddr r)"

definition det_equiv_TLBRecord :: "TLBRecord \<Rightarrow> TLBRecord \<Rightarrow> bool" where
  "det_equiv_TLBRecord l r \<equiv>
     det_equiv_Permissions (TLBRecord_perms l) (TLBRecord_perms r) \<and>
     TLBRecord_nG l = TLBRecord_nG r \<and>
     TLBRecord_contiguous l = TLBRecord_contiguous r \<and>
     TLBRecord_level l = TLBRecord_level r \<and>
     TLBRecord_blocksize l = TLBRecord_blocksize r \<and>
     det_equiv_DescriptorUpdate (TLBRecord_descupdate l) (TLBRecord_descupdate r) \<and>
     TLBRecord_CnP l = TLBRecord_CnP r \<and>
     det_equiv_AddressDescriptor (TLBRecord_addrdesc l) (TLBRecord_addrdesc r)"

lemmas det_equiv_defs =
  det_equiv_Fault_def det_equiv_Permissions_def det_equiv_DescriptorUpdate_def det_equiv_AddressDescriptor_def
  det_equiv_MemoryAttributes_def det_equiv_MemAttrHints_def det_equiv_TLBRecord_def

subsection \<open>Lemmas about auxiliary functions of our pure characterisation\<close>

lemma grainsize_cases:
  obtains "grainsize (read_params high s) = 12"
    | "grainsize (read_params high s) = 14"
    | "grainsize (read_params high s) = 16"
  by (fastforce simp: read_params_def Let_def split: if_splits)

lemma outputsize_calc_outputsize:
  "outputsize (read_params high s) =
   calc_outputsize (Word.slice 32 (TCR_EL1 (regstate s))) (largegrain (read_params high s))"
  by (auto simp: read_params_def Let_def)

lemma fst_calc_firstblocklevel_grainsize[simp]:
  "fst (calc_firstblocklevel_grainsize (largegrain (read_params high s))
                                       (midgrain (read_params high s))) =
   firstblocklevel (read_params high s)"
  by (auto simp: calc_firstblocklevel_grainsize_def read_params_def Let_def)

lemma snd_calc_firstblocklevel_grainsize[simp]:
  "snd (calc_firstblocklevel_grainsize (largegrain (read_params high s))
                                       (midgrain (read_params high s))) =
   grainsize (read_params high s)"
  by (auto simp: calc_firstblocklevel_grainsize_def read_params_def Let_def)

lemma grainsize_bounds[simp]:
  "0 \<le> grainsize (read_params high s)"
  "3 \<le> nat (grainsize (read_params high s))"
  "nat (grainsize (read_params high s)) \<le> 48"
  by (auto simp: read_params_def Let_def)

lemma PrePostE_baseaddress[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (baseaddress baseregister baselowerbound_arg outputsize_arg) s)
            (liftS (calc_baseaddress baseregister baselowerbound_arg outputsize_arg)) Q E"
  by (strong_cong_simp add: baseaddress_def calc_baseaddress_def)
     (PrePostAuto simp: max_absorb1 max_absorb2)

lemma startlevel_bounds[simp]:
  "startlevel (read_params high s) \<ge> 0"
  "startlevel (read_params high s) < 4"
  unfolding startlevel_def calc_startlevel_def[unfolded ceiling_divide_eq_div]
  by (auto simp: read_params_def Let_def)

lemma aligned8_baseaddress[simp]:
  fixes high :: bool and s :: "regstate sequential_state"
  defines "p \<equiv> read_params high s"
  shows "aligned (baseaddress baseregister (baselowerbound p) (outputsize p)) 8"
proof -
  have "baselowerbound p \<ge> 3"
    unfolding baselowerbound_def startlevel_def calc_startlevel_def[unfolded ceiling_divide_eq_div]
    by (auto simp: p_def read_params_def Let_def)
  then show ?thesis
    by (auto simp: baseaddress_def Let_def place_slice_def aligned8_simps)
qed

lemma PrePostE_WalkAttrDecode:
  shows "PrePostE (\<lambda>s. \<forall>r. det_equiv_MemoryAttributes r (read_WalkAttrDecode SH_arg ORGN_arg IRGN_arg secondstage s) \<longrightarrow> Q r s)
                  (liftS (WalkAttrDecode SH_arg ORGN_arg IRGN_arg secondstage)) Q E"
  by (strong_cong_simp add: WalkAttrDecode_def read_WalkAttrDecode_def undefined_defs ShortConvertAttrsHints_def
                            S1CacheDisabled_def S2CacheDisabled_def MemAttrDefaults_def liftState_simp and_boolS_returnS_if,
      PrePost simp: fun2_if_distrib[where f = Q])
     (cases IRGN_arg rule: exhaustive_2_word; cases ORGN_arg rule: exhaustive_2_word;
      strong_cong_simp add: det_equiv_MemoryAttributes_def det_equiv_MemAttrHints_def MemoryAttributes.splits;
      repeat_all_new \<open>split if_split_asm if_split; strong_cong_simp?\<close>)

lemma PrePostE_S1CacheDisabled[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. Q (read_S1CacheDisabled acctype s) s) (liftS (S1CacheDisabled acctype)) Q E"
  by (strong_cong_simp add: S1CacheDisabled_def read_S1CacheDisabled_def)
     (PrePostAuto simp: fun2_if_distrib[where f = Q])

lemma PrePostE_LongConvertAttrsHints[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. attrfield \<noteq> 0 \<and>
                       (\<forall>r. det_equiv_MemAttrHints r (read_LongConvertAttrsHints attrfield acctype s) \<longrightarrow> Q r s))
                  (liftS (LongConvertAttrsHints attrfield acctype)) Q E"
  by (strong_cong_simp add: LongConvertAttrsHints_def read_LongConvertAttrsHints_def undefined_defs)
     (PrePost;
      cases attrfield rule: exhaustive_4_word;
      auto simp: MemAttrHints.splits slice_shiftr det_equiv_MemAttrHints_def)

lemma PrePostE_AArch64_S1AttrDecode[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. \<forall>r. det_equiv_MemoryAttributes r (read_S1AttrDecode SH_arg attr acctype s) \<longrightarrow> Q r s)
                  (liftS (AArch64_S1AttrDecode SH_arg attr acctype)) Q E"
  by (strong_cong_simp add: AArch64_S1AttrDecode_def undefined_defs Unreachable_def ConstrainUnpredictableBits_def
                            liftState_simp if_distrib[where f = returnS, symmetric] if_distrib[where f = ucast]
                            word_slice_if_distrib)
     (ParametricPrePost \<open>rule PrePostE_if_branch\<close>
                         \<open>strong_cong_simp add: PrePost_if_distribs app_if_distrib\<close>
                         \<open>auto simp: read_S1AttrDecode_def Let_def word4_and3_exhaust'
                                     det_equiv_MemoryAttributes_def det_equiv_MemAttrHints_def
                                     MemoryAttributes.splits MemAttrHints.splits split: if_splits\<close>
                         atomI: PrePostE_chooseS_any)

lemma InUserMode_MMUEnabled_Not_IsInHost_EL0[simp]:
  assumes "InUserMode s" and "MMUEnabled_EL01 s"
  shows "\<not>read_ELIsInHost 0 s"
  using assms by (auto simp: read_ELIsInHost_def)

lemma PrePostE_Parameters_EL0[PrePostE_atomI]:
  fixes inputaddr :: "64 word" and top :: int
  defines "high \<equiv> inputaddr !! nat top"
  defines "p \<equiv> \<lambda>s. read_params high s"
  shows "PrePostE (\<lambda>s. InUserMode s \<and> MMUEnabled_EL01 s \<and> 0 \<le> top \<and> top < 64 \<and>
                       (\<forall>attrs. det_equiv_MemoryAttributes attrs (read_WalkAttrDecode (SH (p s)) (ORGN (p s)) (IRGN (p s)) secondstage s) \<longrightarrow>
                        Q (valid_vaddr inputaddr top s,
                           read_TTBR high s,
                           descaddr\<lparr>AddressDescriptor_memattrs := attrs\<rparr>,
                           if high then TCR_EL1 (regstate s) !! 23 else TCR_EL1 (regstate s) !! 7,
                           if high then TCR_EL1 (regstate s) !! 42 else TCR_EL1 (regstate s) !! 41,
                           inputsize (p s),
                           largegrain (p s),
                           midgrain (p s)) s))
                  (liftS (Parameters_EL0 descaddr secondstage top inputaddr c)) Q E"
  by (strong_cong_simp add: Parameters_EL0_def IsOnes_slice_def IsZero_slice_def high_def p_def read_TTBR_def)
     (PrePost atomI: PrePostE_WalkAttrDecode simp: fun2_if_distrib[where f = Q],
      auto simp: read_params_def Let_def valid_vaddr_def split del: if_split split: if_split_asm,
      auto simp: max_absorb1 max_absorb2 min_absorb1 min_absorb2 split: if_splits)

lemma length_read_table[simp]:
  "length (read_table level high baseaddr s) = 2 ^ nat (stride level (read_params high s))"
  by (auto simp: Let_def nat_power_eq)

declare read_table.simps[simp del]

lemma nth_read_table_read_descriptor:
  assumes "read_table level high baseaddr s ! nat i = Descriptor desc"
    and "nat i < 2 ^ nat (stride level (read_params high s))" and "0 \<le> i"
  shows "read_descriptor (baseaddr OR (word_of_int i << 3)) s = Some desc"
proof -
  have "[0..2 ^ nat (stride level (read_params high s)) - 1] ! nat i = 0 + int (nat i)"
    using assms
    by (intro nth_upto) (auto simp: nat_less_iff)
  then show ?thesis
    using assms
    unfolding read_table.simps[of level]
    by (auto simp: Let_def nat_power_eq nat_0_le read_descriptor_def split: option.splits if_splits)
qed

lemma read_descriptor_Some_elim:
  assumes "read_descriptor addr s = Some desc"
  obtains w where "read_bigendian s" and "w = reverse_endianness desc" and "read_mem_word addr 8 s = Some w"
  | "\<not>read_bigendian s" and "read_mem_word addr 8 s = Some desc"
  using assms by (auto simp: read_descriptor_def split: option.split_asm if_split_asm)

lemma addrselecttop_level_plus_one[simp]:
  fixes high :: bool and s :: "regstate sequential_state"
  defines "p \<equiv> read_params high s"
  assumes level: "level \<ge> startlevel p"
  shows "addrselecttop (level + 1) p = (3 - level) * (grainsize p - 3) + (grainsize p) - 1"
  using level
  unfolding p_def calc_startlevel_def[unfolded ceiling_divide_eq_div] startlevel_def
  by (auto simp: addrselecttop_def read_params_def Let_def min_def split: if_splits)

lemma addrselecttop_startlevel[simp]:
  fixes high :: bool and s :: "regstate sequential_state"
  defines "p \<equiv> read_params high s"
  shows "addrselecttop (startlevel p) p = inputsize p - 1"
  unfolding p_def calc_startlevel_def[unfolded ceiling_divide_eq_div] startlevel_def
  (* Takes a minute *)
  by (auto simp: addrselecttop_def read_params_def Let_def min_def)

lemma read_table_aligned_baseaddr:
  assumes "read_table level high baseaddr s ! nat i = Table baseaddr' ns ap1 ap0 xn pxn table"
    and "nat i < 2 ^ nat (stride level (read_params high s))" and "0 \<le> i"
    and "aligned baseaddr 8"
  shows "aligned baseaddr' 8"
proof -
  have "[0..2 ^ nat (stride level (read_params high s)) - 1] ! nat i = 0 + int (nat i)"
    using assms
    by (intro nth_upto) (auto simp: nat_less_iff)
  then show ?thesis
    using assms(1)[symmetric] assms(2,3,4)
    unfolding read_table.simps[of level]
    by (auto simp: Let_def nat_power_eq nat_0_le aligned8_simps split: if_split_asm option.split_asm)
qed

lemma walk_table_aligned_descaddr:
  assumes "walk_table inputaddr level p baseaddr (read_table level high baseaddr s) = Some (desc, descaddr, rest)"
    and "aligned baseaddr 8"
  shows "aligned descaddr 8"
  using assms
proof (induction inputaddr level p baseaddr "read_table level high baseaddr s" arbitrary: rest rule: walk_table.induct)
  case (1 inputaddr level p baseaddr)
  then show ?case
    unfolding walk_table.simps[where level = level]
    (* Takes a minute *)
    by (auto simp: Let_def aligned8_simps read_table_aligned_baseaddr
             split: if_split_asm option.split_asm TableEntry.split_asm;
        simp add: read_table.simps[where level = level] Let_def nat_power_eq nat_0_le;
        auto split: option.split_asm if_split_asm simp: Let_def)
qed

lemma lookup_TLBRecord_no_fault_aligned[simp]:
  assumes "lookup_TLBRecord vaddress acctype s = Some r"
  shows "FaultRecord_typ (AddressDescriptor_fault (TLBRecord_addrdesc r)) = Fault_None"
    and "FaultRecord_typ (AddressDescriptor_fault (DescriptorUpdate_descaddr (TLBRecord_descupdate r))) = Fault_None"
    and "aligned (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r))) 8"
  using assms aligned8_baseaddress[where high = "vaddress !! nat (read_AddrTop_EL0 vaddress (acctype = AccType_IFETCH) s)" and s = s]
  (* Takes a minute *)
  by (auto simp: lookup_TLBRecord_def Let_def walk_table_aligned_descaddr
           simp del: aligned8_baseaddress split: option.split_asm if_split_asm)

lemma walk_table_desc_eq_read_descriptor_descaddr[simp]:
  assumes "walk_table inputaddr level p baseaddr (read_table level high baseaddr s) = Some (desc, descaddr, rest)"
  shows "read_descriptor descaddr s = Some desc"
  using assms
proof (induction inputaddr level p baseaddr "read_table level high baseaddr s" arbitrary: rest rule: walk_table.induct)
  case (1 inputaddr level p baseaddr)
  then show ?case
    unfolding walk_table.simps[where level = level]
  (* Takes a minute *)
    by (auto simp: Let_def nth_read_table_read_descriptor split: if_split_asm option.split_asm TableEntry.split_asm;
        simp add: read_table.simps[where level = level] Let_def nat_power_eq nat_0_le;
        auto split: option.split_asm if_split_asm simp: Let_def)
qed

lemma lookup_TLBRecord_read_descriptor[simp]:
  assumes "lookup_TLBRecord vaddress acctype s = Some r"
  shows "\<exists>desc. read_descriptor (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r))) s = Some desc"
  using assms[symmetric]
  by (auto simp: lookup_TLBRecord_def Let_def split: option.split_asm if_split_asm)

lemma regstate_update_descriptor[simp]:
  "regstate (update_descriptor descupd acctype iswrite s) = regstate s"
  by (auto simp: update_descriptor_def Let_def write_mem_bytes_def write_descriptor_def split: option.splits)

lemma det_equiv_TLBRecord_simps[simp]:
  assumes "det_equiv_TLBRecord r' r"
  shows "MemoryAttributes_typ (AddressDescriptor_memattrs (TLBRecord_addrdesc r')) =
         MemoryAttributes_typ (AddressDescriptor_memattrs (TLBRecord_addrdesc r))"
    and "FaultRecord_typ (AddressDescriptor_fault (TLBRecord_addrdesc r')) =
         FaultRecord_typ (AddressDescriptor_fault (TLBRecord_addrdesc r))"
    and "FaultRecord_typ (AddressDescriptor_fault (DescriptorUpdate_descaddr (TLBRecord_descupdate r'))) =
         FaultRecord_typ (AddressDescriptor_fault (DescriptorUpdate_descaddr (TLBRecord_descupdate r)))"
    and "AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r')) =
         AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r))"
    and "valid_perms (TLBRecord_perms r') acctype iswrite s =
         valid_perms (TLBRecord_perms r) acctype iswrite s"
    and "update_descriptor (TLBRecord_descupdate r') acctype iswrite s =
         update_descriptor (TLBRecord_descupdate r) acctype iswrite s"
  using assms by (strong_cong_simp add: det_equiv_defs valid_perms_def update_descriptor_def)+

lemma all_det_equiv_TLBRecord_elim:
  assumes "\<forall>r'. det_equiv_TLBRecord r' r \<longrightarrow> Q (f r') s"
    and "det_equiv_TLBRecord r' r"
  shows "Q (f r') s"
  using assms by blast

subsection \<open>Table walk loop: termination and invariant\<close>

lemma TranslationTableWalk_untilM_domI:
  assumes "TranslationTableWalk_loop_termination_precond vars"
  shows "untilM_dom (vars, TranslationTableWalk_loop_cond,
                     TranslationTableWalk_loop_body singlepriv apply_nvnv1_effect hierattrsdisabled
                       largegrain_arg outputsize_arg ipaddress reversedescriptors s2fs1walk iswrite acctype
                       vaddress False inputaddr grainsize_arg stride_arg)"
proof (rule untilM_domI)
  from assms show "TranslationTableWalk_loop_termination_precond vars" .
next
  fix vars t vars' and t' :: "register_value event list"
  assume "TranslationTableWalk_loop_termination_precond vars"
    and "Run (TranslationTableWalk_loop_body singlepriv apply_nvnv1_effect hierattrsdisabled
                 largegrain_arg outputsize_arg ipaddress reversedescriptors s2fs1walk iswrite acctype
                 vaddress False inputaddr grainsize_arg stride_arg vars)
             t vars'"
    and "Run (TranslationTableWalk_loop_cond vars') t' False"
  then show "TranslationTableWalk_loop_variant vars' < TranslationTableWalk_loop_variant vars \<and>
             TranslationTableWalk_loop_termination_precond vars'"
    unfolding TranslationTableWalk_loop_body_def TranslationTableWalk_loop_cond_def
      TranslationTableWalk_loop_termination_precond_def TranslationTableWalk_loop_variant_def
    (* Takes a minute *)
    by (elim Run_letE Run_case_prodE Run_bindE_ignore_trace Run_ifE Run_returnE Run_early_returnE
             Run_or_boolM_E Run_and_boolM_E)
       auto
qed

lemma PrePostE_TranslationTableWalk_loop:
  fixes inputaddr :: "64 word" and vaddress :: "64 word" and grainsize_arg :: int and outputsize_arg :: int
    and stride_arg :: int and singlepriv :: bool and hierattrsdisabled :: bool
    and apply_nvnv1_effect :: bool and acctype :: AccType and iswrite :: bool and s2fs1walk :: bool
    and reversedescriptors :: bool and ipaddress :: "52 word" and largegrain_arg :: bool
  defines "high \<equiv> \<lambda>s. inputaddr !! nat (read_AddrTop_EL0 inputaddr (acctype = AccType_IFETCH) s)"
  defines "p \<equiv> \<lambda>s. read_params (high s) s"
  defines "Inv \<equiv> \<lambda>Q (accdesc, addrselectbottom_arg, addrselecttop_arg, ap_table, baseaddress,
                     blocktranslate, desc, descaddr, descaddr2, hwupdatewalk, level,
                     ns_table, pxn_table, result, xn_table) s.
                   largegrain (p s) = largegrain_arg \<and>
                   outputsize (p s) = outputsize_arg \<and>
                   read_bigendian s = reversedescriptors \<and>
                   grainsize_arg = grainsize (p s) \<and>
                   grainsize_arg - 3 = stride_arg \<and>
                   addrselecttop level (p s) = addrselecttop_arg \<and>
                   \<not>singlepriv \<and>
                   level \<ge> startlevel (p s) \<and>
                   level < 4 \<and> \<not>IsFault descaddr \<and> UsingAArch64 s \<and>
                   NonSecure_EL01 s \<and> \<not>S2TranslationEnabled s \<and> aligned baseaddress 8 \<and>
                   (case walk_table inputaddr level (p s) baseaddress (read_table level (high s) baseaddress s)
                    of Some (desc, descaddr', baseaddress, level, ns', ap1', ap0', xn', pxn') \<Rightarrow>
                         (let descaddr = descaddr\<lparr>AddressDescriptor_paddress :=
                                                    AddressDescriptor_paddress descaddr
                                                      \<lparr>FullAddress_physicaladdress := descaddr',
                                                       FullAddress_NS := of_bl [ns_table !! 0 \<or> ns']\<rparr> \<rparr>;
                              descaddr2 = descaddr\<lparr>AddressDescriptor_vaddress := vaddress\<rparr>;
                              ns_table = of_bl [ns_table !! 0 \<or> ns'];
                              ap_table = of_bl [ap_table !! Suc 0 \<or> \<not>hierattrsdisabled \<and> ap1',
                                                ap_table !! 0 \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> ap0'];
                              xn_table = of_bl [xn_table !! 0 \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> xn'];
                              pxn_table = of_bl [pxn_table !! 0 \<or>
                                                 \<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> xn' \<or>
                                                 \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> pxn'] in
                          (\<forall>s2fs1walk. Q (AccessDescriptor acctype True False s2fs1walk level,
                                          addrselectbottom level (p s), addrselecttop level (p s),
                                          ap_table, baseaddress, True, desc, descaddr, descaddr2,
                                          False, level, ns_table, pxn_table, result, xn_table) s))
                     | None \<Rightarrow> False)"
  defines "body \<equiv> TranslationTableWalk_loop_body singlepriv apply_nvnv1_effect hierattrsdisabled
                    largegrain_arg outputsize_arg ipaddress reversedescriptors s2fs1walk iswrite acctype
                    vaddress False inputaddr grainsize_arg stride_arg"
  shows "PrePostE (Inv Q vars) (liftS (untilM vars TranslationTableWalk_loop_cond body)) Q E"
proof -
  let ?blocktranslate = "\<lambda>vars. fst (snd (snd (snd (snd (snd vars)))))"
  note simps = PAMax_simp undefined_int_def IsZero_slice_def IsOnes_slice_def CreateAccessDescriptorPTW_def
  have cond: "TranslationTableWalk_loop_cond = return \<circ> ?blocktranslate"
    by (auto simp: TranslationTableWalk_loop_cond_def split: prod.splits)
  have body: "PrePostE (Inv Q vars) (liftS (body vars))
                       (\<lambda>vars' s'. Inv Q vars' s' \<and> (?blocktranslate vars' \<longrightarrow> Q vars' s')) E" for vars
  proof (cases vars rule: prod15_cases)
    case (1 accdesc addrselectbottom addrselecttop ap_table baseaddress blocktranslate desc
            descaddr descaddr2 hwupdatewalk level ns_table pxn_table result xn_table)
    have ap_table:
      "(if ucast desc = (1 :: 2 word) \<or> level = 3 then ap_table else
        if \<not>hierattrsdisabled then
          if \<not> singlepriv then
            if \<not> apply_nvnv1_effect
              then of_bl [ap_table !! Suc 0 \<or> desc !! 62, ap_table !! 0 \<or> desc !! 61]
              else of_bl [ap_table !! Suc 0 \<or> desc !! 62, ap_table !! 0]
          else of_bl [ap_table !! Suc 0 \<or> desc !! 62, ap_table !! 0]
        else ap_table) =
       (if ucast desc = (1 :: 2 word) \<or> level = 3 then ap_table else
        of_bl [ap_table !! Suc 0 \<or>
               \<not>hierattrsdisabled \<and> desc !! 62, ap_table !! 0 \<or>
               \<not>hierattrsdisabled \<and> \<not>singlepriv \<and> \<not>apply_nvnv1_effect \<and> desc !! 61])"
      for desc :: "64 word"
      by auto
    have pxn_table:
      "(if ucast desc = (1 :: 2 word) \<or> level = 3 then pxn_table else
        if \<not>hierattrsdisabled then
          if \<not> singlepriv then
            if \<not> apply_nvnv1_effect then of_bl [pxn_table !! 0 \<or> desc !! 59] else
              if apply_nvnv1_effect then of_bl [pxn_table !! 0 \<or> desc !! 60] else pxn_table
          else if apply_nvnv1_effect then of_bl [pxn_table !! 0 \<or> desc !! 60] else pxn_table
        else pxn_table) =
       (if ucast desc = (1 :: 2 word) \<or> level = 3 then pxn_table else
        of_bl [pxn_table !! 0 \<or>
               \<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> desc !! 60 \<or>
               \<not>hierattrsdisabled \<and> \<not>singlepriv \<and> \<not>apply_nvnv1_effect \<and> desc !! 59])"
      for desc :: "64 word"
      by auto
    have xn_table:
      "(if ucast desc = (1 :: 2 word) \<or> level = 3 then xn_table else
        if \<not>hierattrsdisabled then
          if apply_nvnv1_effect then xn_table
          else of_bl [xn_table !! 0 \<or> desc !! 60]
        else xn_table) =
       (if ucast desc = (1 :: 2 word) \<or> level = 3 then xn_table
        else of_bl [xn_table !! 0 \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> desc !! 60])"
      for desc :: "64 word"
      by auto
    have swap_pxn:
      "\<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> xn \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> pxn \<or>
       \<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> xn' \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> pxn'
       \<longleftrightarrow>
       \<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> xn \<or> \<not>hierattrsdisabled \<and> apply_nvnv1_effect \<and> xn' \<or>
       \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> pxn \<or> \<not>hierattrsdisabled \<and> \<not>apply_nvnv1_effect \<and> pxn'"
      for xn xn' pxn pxn'
      by auto
    have merge_if_branches:
      "(if c1 then bindS m1 f1 else (if c2 then returnS v1 else (if c3 then bindS m2 f2 else returnS v2))) =
       (if c1 \<or> (\<not>c1 \<and> \<not>c2 \<and> c3) then (if c1 then bindS m1 f1 else bindS m2 f2) else (if c2 then returnS v1 else returnS v2))"
      for c1 c2 c3 f1 v1 f2
        and m1 :: "(regstate, FaultRecord, TLBRecord, exception) monadRS"
        and m2 :: "(regstate, FaultRecord, TLBRecord, exception) monadRS"
        and v2 :: "(int \<times> 2 word \<times> 52 word \<times> bool \<times> int \<times> 1 word \<times> 1 word \<times> TLBRecord \<times> 1 word)"
      by auto
    show ?thesis
      using 1
      (* Takes a few minutes *)
      by (strong_cong_simp add: body_def TranslationTableWalk_loop_body_def simps
                                ZeroExtend_slice_append_simp place_slice_grainsize
                                undefined_defs
                                PrePost_if_distribs Let_def test_bit_of_bl liftState_simp
                                merge_if_branches fun2_if_distrib[where f = bindS]
                                if_distrib[where f = liftRS, symmetric] CreateFaultRecord_if_distrib)
         (PrePost compositeI: PrePostE_bindS_HasS2Translation_True PrePostE_bindS_prods
                                 PrePostE_bindS_any_simp
                   atomI: PrePostE_AArch64_SecondStageWalk_disabled PrePostE_chooseS_any
                   simp: PrePost_if_distribs app_case_distribs fun2_if_distrib[where f= "Inv Q"],
          unfold ap_table pxn_table xn_table,
          cases reversedescriptors; cases "level = 3";
          simp add: Inv_def split del: if_split;
          elim conjE option_case_prod_9_None_False_elim;
          use walk_table.simps[where level = level] read_table.simps[where level = level] in
          \<open>strong_cong_simp add: Inv_def IsFault_def if_distrib[where f = "\<lambda>c. aligned c 8"]
                                 aligned8_OR_distrib aligned8_shiftl_3 aligned8_word_cat
                                 aligned8_ucast[unfolded ucast_def] place_slice_grainsize ucast_def
                                 addrselectbottom_def stride_def
                                 ValidDescriptor_def p_def Let_def
                                 cong: TableEntry.case_cong\<close>;
          repeat_all_new \<open>split option.split_asm TableEntry.split_asm if_split_asm; (strong_cong_simp add: ucast_def)?\<close>;
          auto simp: test_bit_of_bl conj_disj_distribL swap_pxn)
  qed
  moreover have "untilM_dom (vars, TranslationTableWalk_loop_cond, body)" if "Inv Q vars s" for s
    using that startlevel_bounds(1)[THEN order.trans] unfolding body_def
    by (intro TranslationTableWalk_untilM_domI)
       (auto simp: TranslationTableWalk_loop_termination_precond_def Inv_def p_def)
  ultimately show ?thesis
    unfolding cond
    by (intro PrePostE_liftState_untilM_pure_cond; blast)
qed

subsection \<open>Hoare triples for different parts of address translation\<close>

lemma PrePostE_AArch64_TranslationTableWalk_usermode_NoFault:
  shows "PrePostE (\<lambda>s. InUserMode s \<and> NonSecure_EL01 s \<and> MMUEnabled_EL01 s \<and> VirtDisabled s \<and>
                       HwUpdatesFlags s \<and> UsingAArch64 s \<and>
                       (case lookup_TLBRecord vaddress acctype s of
                              None \<Rightarrow> False
                            | Some r \<Rightarrow> \<forall>r'. det_equiv_TLBRecord r' r \<longrightarrow> Q r' s))
                  (liftS (AArch64_TranslationTableWalk ipaddress vaddress acctype iswrite False s2fs1walk size1))
                  Q E"
    (is "PrePostE ?P ?m Q E")
proof (rule PrePostE_post_mp)
  note compositeI = PrePostE_bindS_TLBRecords PrePostE_bindS_prods PrePostE_PSTATE_EL_0 PrePostE_bindS_IsInHost_False
                    PrePostE_readS_pred[where f = "\<lambda>s. TCR_EL1 (regstate s)",
                                        THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. \<not>a !! 7 \<and> \<not>a !! 23 \<and> a !! 39 \<and> a !! 40"]
                    PrePostE_readS_pred[where f = "\<lambda>s. HCR_EL2 (regstate s)",
                                        THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. \<not>a !! 0 \<and> \<not>a !! 12 \<and> \<not>a !! 42 \<and> \<not>a !! 43"]
                    PrePostE_bindS_any[where m = "liftRS \<lbrakk>AddrTop vaddress (acctype = AccType_IFETCH) el\<rbrakk>\<^sub>S" for el]
                    PrePostE_bindS_any[where m = "liftRS \<lbrakk>ELUsingAArch32 el\<rbrakk>\<^sub>S" for el]
  note simps = PrePost_if_distribs app_case_distribs TLBRecord_if_distrib DescriptorUpdate_if_distrib
               IsFault_def aligned8_simps place_slice_grainsize read_S1TranslationRegime_def
               fun2_if_distrib[where f = Q] if_then_conj_distrib
               if_distrib[where f = "\<lambda>c. c\<lparr>DescriptorUpdate_descaddr := x\<rparr>" for x]
               if_distrib[where f = "\<lambda>c. t = c" for t :: TLBRecord]
               if_distrib[where f = "\<lambda>c. w = c" for w :: "1 word", symmetric]
               startlevel_def[symmetric] baselowerbound_def[symmetric]
               PAMax_simp undefined_int_def IsZero_slice_def IsOnes_slice_def CreateAccessDescriptorPTW_def
  note atomI = PrePostE_AArch64_S1AttrDecode PrePostE_TranslationTableWalk_loop PrePostE_WalkAttrDecode PrePostE_AddrTop_EL0 PrePostE_chooseS_any
  note main_def = AArch64_TranslationTableWalk_def[folded TranslationTableWalk_loop_body_def
                                                          TranslationTableWalk_loop_cond_def
                                                          calc_outputsize_def
                                                          Parameters_EL0_def
                                                          calc_startlevel_def
                                                          calc_firstblocklevel_grainsize_def
                                                          calc_baseaddress_def
                                                          calc_outputsize_def
                                                          calc_contiguousbitcheck_def]
  note unfolds = liftState_simp IsFault_def undefined_defs undefined_bitvector_simp
                 ZeroExtend__1_64_64_return comp_def liftState_let_distrib liftState_prod_distrib
                 bindS_assoc liftRS_bindS liftRS_returnS bindS_returnS_left if_distrib[where f = returnS, symmetric]
                 ex_int_def undefined_bitvector_simp bind_return Have_simps ZeroExtend_simps
                 and_boolM_simps and_boolM_if_distrib or_boolM_simps or_boolM_if_distrib
                 liftR_undefined_bool liftR_return liftR_read_reg assert_exp_True_return
                 PAMax_simp undefined_int_def IsZero_slice_def IsOnes_slice_def CreateAccessDescriptorPTW_def
  show "PrePostE ?P ?m (\<lambda>r s. \<not>IsFault (TLBRecord_addrdesc r)) E"
    unfolding main_def unfolding unfolds
    using [[linarith_split_limit = 20]]
    (* Takes a few minutes *)
    by (rule PrePostE_strengthen_pre,
        ComputePre \<open>rule compositeI\<close> \<open>strong_cong_simp add: simps\<close> - atomI: atomI)
       (simp add: lookup_TLBRecord_def TTBR_valid_for_vaddr_def
                  read_SCTLR_def Let_def outputsize_calc_outputsize
                  aligned8_baseaddress[unfolded outputsize_calc_outputsize]
             split del: if_split split: option.splits cong: if_cong)
  have all_equivE: "Q r' s"
    if "\<forall>r'. det_equiv_TLBRecord r' r \<longrightarrow> Q r' s" and "det_equiv_TLBRecord r' r" for s r r'
    using that by blast
  show "PrePostE ?P ?m (\<lambda>r s. \<not> IsFault (TLBRecord_addrdesc r) \<longrightarrow> Q r s) E"
    unfolding main_def unfolding unfolds case_None_False_exists_Some
    using [[linarith_split_limit = 20]]
    (* Takes a few minutes *)
    by (rule PrePostE_strengthen_pre,
        ComputePre \<open>ComputePre_if_heuristic | rule compositeI\<close> \<open>strong_cong_simp add: simps\<close> - atomI: atomI)
       (elim conjE exE;
        simp add: lookup_TLBRecord_def read_SCTLR_def Let_def
                  outputsize_calc_outputsize[symmetric] addrselectbottom_def[symmetric]
                  pow2_def pow_def of_bl_AND_of_bl test_bit_set_gen set_bit_3_word
                  test_bit_of_bl nth_word_cat nth_slice to_bl_1_1word
                  if_distrib[where f = test_bit] if_distrib[where f = "\<lambda>c. Word.slice n c" for n]
                  app_if_distrib slice_set_bit_below slice_set_bit_above
                  Some_eq_if_Some_None_iff_eq
                  split del: if_split split: option.splits cong: if_cong;
        fastforce elim!: all_equivE simp: det_equiv_defs)
qed

lemma PrePostE_AArch64_CheckAndUpdateDescriptor:
  fixes result :: DescriptorUpdate
  defines "addr \<equiv> AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr result)"
  shows "\<lbrace>\<lambda>s. FaultRecord_typ fault = Fault_None \<and> \<not> IsFault (DescriptorUpdate_descaddr result) \<and>
              aligned (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr result)) 8 \<and>
              UsingAArch64 s \<and>
              NonSecure_EL01 s \<and>
              VirtDisabled s \<and>
              addr \<noteq> 0x13000000 \<and>
              read_descriptor addr s \<noteq> None \<and>
              Q fault (update_descriptor result acctype iswrite s)\<rbrace>
         \<lbrakk>AArch64_CheckAndUpdateDescriptor result fault False vaddress acctype iswrite False False\<rbrakk>\<^sub>S \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_CheckAndUpdateDescriptor_def aset__Mem_def CreateAccessDescriptor_def
                            undefined_defs WriteRAM_def liftState_simp,
      PrePost atomI: PrePostE_write_ram PrePostE_AArch64_SecondStageWalk_disabled)
     (auto simp: addr_def update_descriptor_def Let_def fun2_if_distrib[where f = Q] write_descriptor_def
           elim: read_descriptor_Some_elim split del: if_split split: option.split_asm cong: if_cong)

lemma PrePostE_AArch64_CheckPermission_EL0:
  "\<lbrace>\<lambda>s. valid_perms perms acctype iswrite s \<and>
        read_EL s = 0 \<and> VirtDisabled s \<and> UsingAArch64 s \<and> NonSecure_EL01 s \<and>
        (\<forall>r. FaultRecord_typ r = Fault_None \<longrightarrow> Q r s)\<rbrace>
   \<lbrakk>AArch64_CheckPermission perms vaddress level ns acctype iswrite\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_CheckPermission_def AArch64_PermissionFault_def
                            AArch64_AccessIsPrivileged_def AArch64_ExecutingATS1xPInstr_def
                            ThisInstr0_def IsInHost_def,
      PrePost compositeI: PrePostE_PSTATE_EL_0 PrePostE_bindS_IsInHost_False
              simp: PrePost_if_distribs atomI: PrePostE_any[where m = "\<lbrakk>AArch64_ExecutingATS1xPInstr ()\<rbrakk>\<^sub>S"])
     (auto simp: valid_perms_def Let_def NonSecure_EL01_def read_SCTLR_def read_S1TranslationRegime_def
           split: if_split_asm)

lemma PrePostE_AArch64_FirstStageTranslate_EL0_No_Fault:
  "\<lbrace>\<lambda>s. InUserMode s \<and> NonSecure_EL01 s \<and> MMUEnabled_EL01 s \<and> VirtDisabled s \<and>
        HwUpdatesFlags s \<and> UsingAArch64 s \<and>
        (case translate_address vaddress acctype iswrite wasaligned s of
               None \<Rightarrow> False
             | Some r \<Rightarrow> \<forall>r'. det_equiv_TLBRecord r' r \<longrightarrow>
                              Q (TLBRecord_addrdesc r')
                                (update_descriptor (TLBRecord_descupdate r) acctype iswrite s))\<rbrace>
   \<lbrakk>AArch64_FirstStageTranslate vaddress acctype iswrite wasaligned sz\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
   (is "\<lbrace>?P\<rbrace> ?m \<lbrace>Q \<bar> E\<rbrace>")
proof -
  have det_equiv_FaultRecord_upd:
    "det_equiv_TLBRecord (r'\<lparr>TLBRecord_addrdesc := TLBRecord_addrdesc r'\<lparr>AddressDescriptor_fault := a\<rparr>\<rparr>) r"
    if "det_equiv_TLBRecord r' r"
      and "FaultRecord_typ a = FaultRecord_typ (AddressDescriptor_fault (TLBRecord_addrdesc r'))"
      for a r r'
    using that by (cases r'; cases r) (auto simp: det_equiv_defs)
  note all_det_equiv_TLBRecord_addrdesc =
    all_det_equiv_TLBRecord_elim[OF _ det_equiv_FaultRecord_upd,
      where f = TLBRecord_addrdesc, simplified] thm all_det_equiv_TLBRecord_addrdesc
  show ?thesis
    by (strong_cong_simp add: AArch64_FirstStageTranslate_def AArch64_InstructionDevice_def comp_def
                              AArch64_AlignmentFault_def IsFault_def undefined_defs
                              AArch32_ExecutingLSMInstr_def ThisInstrLength_def CurrentInstrSet_def
                              undefined_InstrSet_def ThisInstr0_def liftState_simp;
        PrePost atomI: PrePostE_AArch64_CheckAndUpdateDescriptor PrePostE_AArch64_CheckPermission_EL0
                       PrePostE_AArch64_TranslationTableWalk_usermode_NoFault
                       PrePostE_any[where m = "\<lbrakk>AArch64_TranslateAddressS1Off vaddress acctype iswrite\<rbrakk>\<^sub>S"]
                compositeI: PrePostE_bindS_HasS2Translation_True PrePostE_bindS_any simp: IsFault_def;
        auto simp: translate_address_def all_det_equiv_TLBRecord_addrdesc split: option.split_asm if_split_asm)
qed

lemma PrePost_AArch64_TranslateAddress:
  "\<lbrace>\<lambda>s. InUserMode s \<and> NonSecure_EL01 s \<and> MMUEnabled_EL01 s \<and> VirtDisabled s \<and>
        HwUpdatesFlags s \<and> UsingAArch64 s \<and> DebugDisabled s \<and>
        (case translate_address vaddress acctype iswrite wasaligned s of
               None \<Rightarrow> False
             | Some r \<Rightarrow> \<forall>r'. det_equiv_TLBRecord r' r \<longrightarrow>
                              Q (Value (TLBRecord_addrdesc r'))
                                (update_descriptor (TLBRecord_descupdate r) acctype iswrite s))\<rbrace>
   \<lbrakk>AArch64_TranslateAddress vaddress acctype iswrite wasaligned sz\<rbrakk>\<^sub>S
   \<lbrace>Q\<rbrace>"
  by (rule PrePostE_PrePost,
      strong_cong_simp add: AArch64_TranslateAddress_def AArch64_FullTranslate_def AArch64_SecondStageTranslate_def,
      PrePost atomI: PrePostE_AArch64_CheckDebug_DebugDisabled PrePostE_AArch64_SecondStageWalk_disabled
                      PrePostE_AArch64_FirstStageTranslate_EL0_No_Fault compositeI: PrePostE_HCR_EL2_s2disabled)
     (auto simp: translate_address_def TLBRecord.splits AddressDescriptor.splits
                 det_equiv_TLBRecord_def det_equiv_AddressDescriptor_def IsFault_def
           split: option.split_asm if_split_asm;
      fastforce simp: FaultRecord.splits det_equiv_Fault_def)

lemma translate_address_Some_no_exception:
  assumes "InUserMode s" "NonSecure_EL01 s" "MMUEnabled_EL01 s" "VirtDisabled s"
    and "HwUpdatesFlags s" "UsingAArch64 s" "DebugDisabled s"
    and "translate_address vaddress acctype iswrite wasaligned s = Some r"
  shows "\<forall>res s'. (res, s') \<in> \<lbrakk>AArch64_TranslateAddress vaddress acctype iswrite wasaligned sz\<rbrakk>\<^sub>S s \<longrightarrow>
                  (\<exists>r. res = Value r)"
  using assms
  by (auto elim: PrePost_elim[OF PrePost_AArch64_TranslateAddress[where Q = "\<lambda>res s'. \<exists>r. res = Value r"], rotated])

subsection \<open>Soundness result\<close>

text \<open>Theorem 8.1 in the paper, proved by instantiating the above Hoare triple:\<close>

theorem translate_address_sound:
  assumes "InUserMode s" "NonSecure_EL01 s" "MMUEnabled_EL01 s" "VirtDisabled s"
    and "HwUpdatesFlags s" "UsingAArch64 s" "DebugDisabled s"
    and "translate_address vaddress acctype iswrite wasaligned s = Some r"
  shows "\<forall>r' s'.
           (Value r', s') \<in> \<lbrakk>AArch64_TranslateAddress vaddress acctype iswrite wasaligned sz\<rbrakk>\<^sub>S s \<longrightarrow>
              det_equiv_AddressDescriptor r' (TLBRecord_addrdesc r) \<and>
              s' = update_descriptor (TLBRecord_descupdate r) acctype iswrite s"
  using assms
  using PrePost_AArch64_TranslateAddress
    [where vaddress = vaddress and acctype = acctype and iswrite = iswrite and wasaligned = wasaligned and sz = sz
     and Q = "\<lambda>res s'. case res of Ex e \<Rightarrow> False
                                 | Value r' \<Rightarrow>
                                     det_equiv_AddressDescriptor r' (TLBRecord_addrdesc r) \<and>
                                     s' = update_descriptor (TLBRecord_descupdate r) acctype iswrite s"]
  by (intro allI impI, elim PrePost_elim)
     (auto simp: det_equiv_TLBRecord_def)

end
