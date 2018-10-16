(*<*)
(* Author: Thomas Bauereiss *)
theory AArch64_Aux
  imports AArch64_Trivia
begin
(*>*)

text \<open>Lemmas about auxiliary functions in the original model, e.g. for reading system registers or
reading and writing memory.\<close>

lemma PrePostE_BigEndianReverse[PrePostE_atomI]:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<in> {8, 16, 32, 64, 128}"
  shows "PrePostE (Q (reverse_endianness w)) (liftS (BigEndianReverse w)) Q E"
  using assms unfolding BigEndianReverse_def
  by (auto simp: liftState_simp)

lemma BigEndianReverse_8_word[simp]: "BigEndianReverse (w :: 8 word) = return w"
  by (auto simp: BigEndianReverse_def index_list.simps update_subrange_vec_dec_def word_update_def)

abbreviation "UsingAArch64 s \<equiv> ProcState_nRW (PSTATE (regstate s)) = 0"

lemma PrePostE_UsingAArch32[PrePostE_atomI]:
  "PrePostE (\<lambda>s. if UsingAArch64 s
                 then Q False s
                 else E (Failure ''!(aarch32)'') s)
            (liftS (UsingAArch32 unit)) Q E"
  by (strong_cong_simp add: UsingAArch32_def HaveAnyAArch32_def HighestELUsingAArch32_def Let_def)
     (PrePost; auto simp: word1_eq_1_neq_0)

lemma PrePostE_ELUsingAArch32[PrePostE_atomI]:
  shows "PrePostE (Q False) (liftS (ELUsingAArch32 el)) Q E"
  by (strong_cong_simp add: ELUsingAArch32_def IsSecureBelowEL3_def aget_SCR_GEN_def
                            HighestELUsingAArch32_def ELStateUsingAArch32_def ELStateUsingAArch32K_def
                            HaveAArch32EL_def HaveAnyAArch32_def)
     (PrePost)

lemma PrePostE_IsSecureBelowEL3[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (\<not>(SCR_EL3 (regstate s) !! 0)) s) (liftS (IsSecureBelowEL3 unit)) Q E"
  by (strong_cong_simp add: IsSecureBelowEL3_def aget_SCR_GEN_def HighestELUsingAArch32_def)
     (PrePost; auto)

abbreviation "read_EL s \<equiv> ProcState_EL (PSTATE (regstate s))"
lemmas [simp] = EL0_def EL1_def EL2_def EL3_def

definition read_ELIsInHost :: "2 word \<Rightarrow> regstate sequential_state \<Rightarrow> bool" where
  "read_ELIsInHost el s \<equiv> SCR_EL3 (regstate s) !! 0 \<and> HCR_EL2 (regstate s) !! 34 \<and>
                          (el = 2 \<or> (el = 0 \<and> HCR_EL2 (regstate s) !! 27))"

lemma PrePostE_ELIsInHost[PrePostE_atomI]:
  fixes el :: "2 word"
  (*assumes "\<And>s. P s \<longleftrightarrow> (\<forall>seed'. Q (ELIsInHostP el s) (s\<lparr>seed := seed'\<rparr>))"*)
  shows "PrePostE (\<lambda>s. Q (read_ELIsInHost el s) s) (liftS (ELIsInHost el)) Q E"
  by (strong_cong_simp add: ELIsInHost_def read_ELIsInHost_def)
     (PrePostAuto simp: app_if_distrib)

definition read_S1TranslationRegime :: "2 word \<Rightarrow> regstate sequential_state \<Rightarrow> 2 word" where
  "read_S1TranslationRegime el s = (if el = 0 then (if read_ELIsInHost 0 s then 2 else 1) else el)"

lemma read_S1TranslationRegime_eq_0_False[simp]: "read_S1TranslationRegime el s = 0 \<longleftrightarrow> False"
  by (auto simp: read_S1TranslationRegime_def)

lemma read_S1TranslationRegime_def_EL0[simp]:
  assumes "read_EL s = 0" and "\<not>read_ELIsInHost 0 s"
  shows "read_S1TranslationRegime 0 s = 1"
  using assms by (auto simp: read_S1TranslationRegime_def)

lemma PrePostE_S1TranslationRegime__0[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. Q (read_S1TranslationRegime el s) s) (liftS (S1TranslationRegime__0 el)) Q E"
  by (strong_cong_simp add: S1TranslationRegime__0_def read_S1TranslationRegime_def)
     (PrePostAuto simp: read_ELIsInHost_def app_if_distrib)

lemma PrePostE_S1TranslationRegime__1[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. Q (read_S1TranslationRegime (read_EL s) s) s) (liftS (S1TranslationRegime__1 unit)) Q E"
  by (simp add: S1TranslationRegime__1_def) PrePost

definition read_SCTLR :: "2 word \<Rightarrow> regstate sequential_state \<Rightarrow> 32 word" where
  "read_SCTLR regime s =
     (if regime = 2 then SCTLR_EL2 (regstate s) else
      if regime = 3 then SCTLR_EL3 (regstate s) else
      SCTLR_EL1 (regstate s))"

lemma PrePostE_aget_SCTLR__0[PrePostE_atomI]:
  "PrePostE (\<lambda>s. if regime = 0 then E (Failure ''FALSE'') s else Q (read_SCTLR regime s) s) (liftS (aget_SCTLR__0 regime)) Q E"
  by (strong_cong_simp add: aget_SCTLR__0_def read_SCTLR_def Unreachable_def)
     (PrePost; cases regime rule: exhaustive_2_word; auto)

lemma PrePostE_aget_SCTLR__1[PrePostE_compositeI]:
  shows "PrePostE (\<lambda>s. Q (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s) s) (liftS (aget_SCTLR__1 unit)) Q E"
  by (strong_cong_simp add: aget_SCTLR__1_def) (PrePostAuto simp: read_SCTLR_def)

fun read_bigendian :: "regstate sequential_state \<Rightarrow> bool" where
  "read_bigendian s = read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 25"

definition read_MAIR :: "2 word \<Rightarrow> regstate sequential_state \<Rightarrow> 64 word" where
  "read_MAIR regime s =
     (if regime = 2 then MAIR_EL2 (regstate s) else
      if regime = 3 then MAIR_EL3 (regstate s) else
      MAIR_EL1 (regstate s))"

lemma PrePostE_aget_MAIR__0[PrePostE_atomI]:
  "PrePostE (\<lambda>s. if regime = 0 then E (Failure ''FALSE'') s else Q (read_MAIR regime s) s) (liftS (aget_MAIR__0 regime)) Q E"
  by (strong_cong_simp add: aget_MAIR__0_def read_MAIR_def Unreachable_def)
     (PrePost; cases regime rule: exhaustive_2_word; auto)

lemma PrePostE_aget_MAIR__1[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. Q (read_MAIR (read_S1TranslationRegime (read_EL s) s) s) s) (liftS (aget_MAIR__1 unit)) Q E"
  by (strong_cong_simp add: aget_MAIR__1_def) (PrePostAuto simp: read_MAIR_def)

definition read_mem_word :: "52 word \<Rightarrow> int \<Rightarrow> 'regstate sequential_state \<Rightarrow> 'n::len word option" where
  "read_mem_word addr len s =
     Option.bind (just_list (map (memstate s) (index_list (uint addr) (uint addr + len - 1) 1)))
                 (\<lambda>bytes. of_bits_method BC_mword (List.concat (rev bytes)))"

lemma PrePostE_read_ram[PrePostE_atomI]:
  shows "PrePostE (\<lambda>s. len \<ge> 0 \<and> (\<exists>w. read_mem_word addr len s = Some w \<and> Q w s)) (liftS (read_ram addrsize len hexRAM addr)) Q E"
  by (strong_cong_simp add: read_ram_def read_mem_def read_mem_bytes_def read_mem_bytesS_def read_mem_word_def liftState_simp)
     (PrePost; auto split: option.splits if_splits simp: bits_of_mem_bytes_def bits_of_bytes_def read_is_exclusive_def just_list_None_member_None)

abbreviation "AddressDescriptor_physicaladdress d \<equiv> FullAddress_physicaladdress (AddressDescriptor_paddress d)"

lemma PrePostE_aget__Mem[PrePostE_atomI]:
  "PrePostE (\<lambda>s. len \<in> {1, 2, 4, 8, 16} \<and> aligned (AddressDescriptor_physicaladdress desc) len \<and>
                 (case read_mem_word (AddressDescriptor_physicaladdress desc) len s of Some w \<Rightarrow> Q w s | None \<Rightarrow> False))
            (liftS (aget__Mem desc len accdesc)) Q E"
  by (strong_cong_simp add: aget__Mem_def Align__1_def Align__0_def ReadRAM_def liftState_simp)
     (PrePostAuto simp: aligned_def of_bl_bin_word_of_int)

definition write_mem_bytes :: "int \<Rightarrow> int \<Rightarrow> (bitU list) list \<Rightarrow> 'regstate sequential_state \<Rightarrow> 'regstate sequential_state" where
  "write_mem_bytes addr len bytes s =
     s\<lparr>memstate := foldl (\<lambda>mem (addr, b). mem(addr := Some b))
                         (memstate s)
                         (zip (index_list addr (addr + len - 1) 1) bytes)\<rparr>"

lemma PrePostE_write_ram:
  "PrePostE (\<lambda>s. case mem_bytes_of_bits BC_mword w of
                   None \<Rightarrow> E (Failure ''write_mem_val'') (s\<lparr>write_ea := Some (Write_plain, uint addr, max len 0)\<rparr>)
                 | Some bytes \<Rightarrow> Q () (write_mem_bytes (uint addr) len bytes (s\<lparr>write_ea := Some (Write_plain, uint addr, max len 0)\<rparr>)))
            (liftS (write_ram addrlen len hexRAM addr w)) Q E"
  by (strong_cong_simp add: write_ram_def liftState_simp write_mem_eaS_def write_mem_valS_def write_mem_bytesS_def, PrePost)
     (auto simp: write_mem_bytes_def max_absorb1 max_absorb2 index_list_simps fun_upd_def split: option.splits)

lemmas undefined_defs = undefined_MemoryAttributes_def undefined_MemType_def
  undefined_DeviceType_def undefined_MemAttrHints_def undefined_Permissions_def
  undefined_Constraint_def undefined_int_def undefined_Fault_def undefined_FaultRecord_def
  undefined_FullAddress_def undefined_DescriptorUpdate_def undefined_AccessDescriptor_def

lemma PrePostE_internal_pickS_any[PrePostE_atomI]:
  "xs \<noteq> [] \<Longrightarrow> PrePostE (\<lambda>s. \<forall>x. Q x s) (internal_pickS xs) Q E"
  by (PrePost atomI: PrePostE_internal_pick)

lemma PrePostE_undefined_AccType_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_AccType unit)) Q E"
  by (strong_cong_simp add: undefined_AccType_def) PrePost

lemma PrePostE_undefined_AddressDescriptor_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_AddressDescriptor unit)) Q E"
  by (strong_cong_simp add: undefined_AddressDescriptor_def undefined_defs) PrePost

lemma PrePostE_undefined_TLBRecord_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_TLBRecord unit)) Q E"
  by (strong_cong_simp add: undefined_TLBRecord_def undefined_defs) PrePost

lemma PrePostE_AArch64_CreateFaultRecord[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord typ1 ipaddress level acctype write1 extflag errortype secondstage s2fs1walk) s)
            (liftS (AArch64_CreateFaultRecord typ1 ipaddress level acctype write1 extflag errortype secondstage s2fs1walk))
            Q E"
  by (strong_cong_simp add: AArch64_CreateFaultRecord_def undefined_defs) PrePost

lemmas PrePostE_PSTATE_EL_0 = PrePostE_readS_pred[where f = "\<lambda>s. PSTATE (regstate s)", THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. ProcState_EL a = 0"]
lemmas PrePostE_PSTATE_EL_01 = PrePostE_readS_pred[where f = "\<lambda>s. PSTATE (regstate s)", THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. ProcState_EL a = 0 \<or> ProcState_EL a = 1"]

definition NonSecure_EL01 :: "regstate sequential_state \<Rightarrow> bool" where
  "NonSecure_EL01 s \<equiv> (read_EL s = 0 \<or> read_EL s = 1) \<and> SCR_EL3 (regstate s) !! 0 \<and> \<not> read_ELIsInHost (read_EL s) s"

lemma PrePostE_IsSecure[PrePostE_atomI]:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> Q (read_EL s = 3 \<or> \<not>(SCR_EL3 (regstate s) !! 0)) s)
            (liftS (IsSecure unit)) Q E"
  by (strong_cong_simp add: IsSecure_def) PrePostAuto

lemma PrePostE_HasS2Translation[PrePostE_atomI]:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> Q (NonSecure_EL01 s) s) (liftS (HasS2Translation unit)) Q E"
  by (strong_cong_simp add: HasS2Translation_def IsInHost_def NonSecure_EL01_def)
     (PrePost simp: app_if_distrib; auto)

lemma PrePostE_HasS2Translation_True:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> NonSecure_EL01 s \<and> Q s) (liftS (HasS2Translation unit)) (\<lambda>r s. r = True \<and> Q s) E"
  by (PrePostAuto )

lemma PrePostE_liftRS_HasS2Translation_True:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> NonSecure_EL01 s \<and> Q s) (liftRS (liftS (HasS2Translation unit))) (\<lambda>r s. r = True \<and> Q s) E"
  by (PrePostAuto)

lemmas PrePostE_bindS_HasS2Translation_True =
  PrePostE_bindS_left_const_simp[OF PrePostE_HasS2Translation_True]
  PrePostE_bindS_left_const_simp[OF PrePostE_liftRS_HasS2Translation_True]

abbreviation S2TranslationEnabled :: "regstate sequential_state \<Rightarrow> bool" where
  "S2TranslationEnabled s \<equiv> HCR_EL2 (regstate s) !! 0 \<or> HCR_EL2 (regstate s) !! 12"

lemmas PrePostE_HCR_EL2_s2disabled =
  PrePostE_readS_pred[where f = "\<lambda>s. HCR_EL2 (regstate s)", THEN PrePostE_bindS_left_pred_simp,
                      where C = "\<lambda>w. \<not>(w !! 0) \<and> \<not>(w !! 12)"]

lemma PrePostE_AArch64_SecondStageWalk_disabled:
  "PrePostE (\<lambda>s. NonSecure_EL01 s \<and> \<not>(S2TranslationEnabled s) \<and> UsingAArch64 s \<and> Q descaddr s)
            (liftS (AArch64_SecondStageWalk descaddr vaddress acctype iswrite sz hwupdatewalk)) Q E"
  by (strong_cong_simp add: AArch64_SecondStageWalk_def AArch64_SecondStageTranslate_def IsInHost_def undefined_defs)
     (PrePost compositeI: PrePostE_HCR_EL2_s2disabled PrePostE_bindS_HasS2Translation_True or_boolS_returnS_if)

lemma PrePostE_AArch64_TranslationFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_Translation ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_TranslationFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_TranslationFault_def) PrePost

lemma PrePostE_AArch64_AddressSizeFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_AddressSize ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_AddressSizeFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_AddressSizeFault_def) PrePost

lemma PrePostE_AArch64_AccessFlagFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_AccessFlag ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_AccessFlagFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_AccessFlagFault_def) PrePost

lemma PrePostE_AArch64_NoFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>iswrite. Q (CreateFaultRecord Fault_None 0 0 AccType_NORMAL iswrite 0 0 False False) s) (liftS (AArch64_NoFault unit)) Q E"
  by (strong_cong_simp add: AArch64_NoFault_def undefined_int_def) PrePost

lemma ZeroExtend_slice_append_simp:
  shows "ZeroExtend_slice_append outlen (xs :: 'x::len word) i l (ys :: 'y::len word) =
         return ((((ucast (xs AND slice_mask outlen i l >> nat i)) << LENGTH('y)) OR ucast ys) :: 'o::len word)"
  by (auto simp: ZeroExtend_slice_append_def ZeroExtend__1_def ZeroExtend__0_def slice_mask_mask)

lemma PrePostE_ZeroExtend_slice_append[PrePostE_atomI]:
  shows "PrePostE (Q ((word_cat ((xs AND slice_mask outlen i l) >> (nat i)) ys) :: 'o::len word))
                  (liftS (ZeroExtend_slice_append outlen (xs :: 'x::len word) i l (ys :: 'y::len word)))
                  Q E"
  by (strong_cong_simp add: ZeroExtend_slice_append_def ZeroExtend__1_def ZeroExtend__0_def word_cat_shiftl_OR slice_mask_def)
     PrePostAuto

lemma PrePostE_bindS_ELIsInHost_False:
  assumes f: "PrePostE P (f False) Q E"
  shows "PrePostE (\<lambda>s. \<not>read_ELIsInHost el s \<and> P s) (bindS (liftS (ELIsInHost el)) f) Q E"
  by (rule PrePostE_bindS_left_const[where a = False and R = P]; PrePostAuto atomI: f)

lemma PrePostE_bindS_IsInHost_False:
  assumes f: "PrePostE P (f False) Q E"
  shows "PrePostE (\<lambda>s. \<not>read_ELIsInHost (read_EL s) s \<and> P s) (bindS (liftRS (liftS (IsInHost unit))) f) Q E"
  unfolding IsInHost_def
  by (rule PrePostE_bindS_left_const[where a = False and R = P]; PrePostAuto atomI: f)

schematic_goal PrePostE_MemAttrDefaults[PrePostE_atomI]:
  shows "PrePostE ?P (liftS (MemAttrDefaults memattrs)) Q E"
  by (strong_cong_simp add: MemAttrDefaults_def undefined_defs liftState_simp)
     (PrePost simp: PrePost_if_distribs fun2_if_distrib[where f = Q] if_then_all_distrib atomI: PrePostE_chooseS_any)

definition read_AddrTop_EL0 :: "64 word \<Rightarrow> bool \<Rightarrow> regstate sequential_state \<Rightarrow> int" where
  "read_AddrTop_EL0 address isinstr s \<equiv>
     (let tbi = TCR_EL1 (regstate s) !! (if address !! 55 then 38 else 37);
          tbd = TCR_EL1 (regstate s) !! (if address !! 55 then 52 else 51) in
      if tbi \<and> (\<not>tbd \<or> \<not>isinstr) then 55 else 63)"

lemma read_AddrTop_EL0_bounds[simp]:
  "0 \<le> read_AddrTop_EL0 address isinstr s" "read_AddrTop_EL0 address isinstr s < 64"
  by (auto simp: read_AddrTop_EL0_def)

lemma PrePostE_AddrTop_EL0:
  "PrePostE (\<lambda>s. read_S1TranslationRegime el s = 1 \<and> Q (read_AddrTop_EL0 address IsInstr s) s) (liftS (AddrTop address IsInstr el)) Q E"
  by (strong_cong_simp add: AddrTop_def liftState_simp)
     (PrePost simp: PrePost_if_distribs fun2_if_distrib[where f = Q] compositeI: PrePostE_bindS_any_simp,
      auto simp: read_AddrTop_EL0_def split: if_splits)

lemma PrePostE_undefined_AddressDescriptor[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>f a b ba bb bc t d bd be bf.
                   Q \<lparr>AddressDescriptor_fault = CreateFaultRecord f 0 0 a ba 0 0 bb b,
                         AddressDescriptor_memattrs =
                           \<lparr>MemoryAttributes_typ = t, MemoryAttributes_device = d,
                              MemoryAttributes_inner = \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = bc\<rparr>,
                              MemoryAttributes_outer = \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = bd\<rparr>,
                              MemoryAttributes_shareable = be, MemoryAttributes_outershareable = bf\<rparr>,
                         AddressDescriptor_paddress = \<lparr>FullAddress_physicaladdress = 0, FullAddress_NS = 0\<rparr>, AddressDescriptor_vaddress = 0\<rparr>
                    s)
            (liftS (undefined_AddressDescriptor unit)) Q E"
  by (strong_cong_simp add: undefined_AddressDescriptor_def undefined_defs liftState_simp) PrePost

lemma PrePostE_HaltOnBreakpointOrWatchpoint_DebugDisabled:
  "\<lbrace>\<lambda>s. DBGEN (regstate s) = LOW \<and> \<not>MDSCR_EL1 (regstate s) !! 15 \<and> UsingAArch64 s \<and> Q False s\<rbrace>
   \<lbrakk>HaltOnBreakpointOrWatchpoint ()\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: HaltingAllowed_def Halted_def DoubleLockStatus_def HaltOnBreakpointOrWatchpoint_def
                            ExternalSecureInvasiveDebugEnabled_def ExternalInvasiveDebugEnabled_def)
     (PrePostAuto)

lemma PrePostE_AArch64_GenerateDebugExceptions_ignore:
  "\<lbrace>\<lambda>s. UsingAArch64 s \<and> (\<forall>r. Q r s)\<rbrace> \<lbrakk>AArch64_GenerateDebugExceptions ()\<rbrakk>\<^sub>S \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_GenerateDebugExceptions_def AArch64_GenerateDebugExceptionsFrom_def
                            Halted_def DoubleLockStatus_def)
     (PrePost simp: app_if_distrib)

lemma PrePostE_AArch64_CheckDebug_DebugDisabled:
  "\<lbrace>\<lambda>s. DBGEN (regstate s) = LOW \<and> \<not>MDSCR_EL1 (regstate s) !! 15 \<and> UsingAArch64 s \<and>
        (\<forall>r. FaultRecord_typ r = Fault_None \<longrightarrow> Q r s)\<rbrace>
   \<lbrakk>AArch64_CheckDebug vaddress acctype iswrite size1\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_CheckDebug_def liftState_simp,
      PrePostAuto atomI: PrePostE_any[of "\<lbrakk>AArch64_CheckWatchpoint vaddress acctype iswrite size1\<rbrakk>\<^sub>S"]
                          PrePostE_any[of "\<lbrakk>AArch64_CheckBreakpoint vaddress size1\<rbrakk>\<^sub>S"]
                          PrePostE_HaltOnBreakpointOrWatchpoint_DebugDisabled
                          PrePostE_AArch64_GenerateDebugExceptions_ignore)

end
