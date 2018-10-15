theory Address_Translation_Orig
  imports "Sail-AArch64.Aarch64_lemmas"
begin

section \<open>Critical parts of original definition\<close>

text \<open>We copy a few parts of the translation table walk function in the original model,
in particular the table walk loop, into individual definitions in order to reason about them
separately.  Note that this just serves to make it easier to state some of the auxiliary
lemmas; the main proof refers only to the original model.\<close>

definition TranslationTableWalk_loop_body ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> 52 word \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> AccType
       \<Rightarrow> 64 word
          \<Rightarrow> bool \<Rightarrow> 64 word
                     \<Rightarrow> int \<Rightarrow> int \<Rightarrow> AccessDescriptor \<times> int \<times> int \<times> 2 word \<times>
                                                       52 word \<times>
                                                       bool \<times>
                                                       64 word \<times> AddressDescriptor \<times> AddressDescriptor \<times> bool \<times> int \<times> 1 word \<times> 1 word \<times> TLBRecord \<times> 1 word
                                      \<Rightarrow> (register_value,
                                          AccessDescriptor \<times>
                                          int \<times> int \<times> 2 word \<times>
                                                       52 word \<times>
                                                       bool \<times>
                                                       64 word \<times>
                                                       AddressDescriptor \<times>
                                                       AddressDescriptor \<times> bool \<times> int \<times> 1 word \<times> 1 word \<times> TLBRecord \<times> 1 word,
                                          TLBRecord + exception) monad" where
  "TranslationTableWalk_loop_body singlepriv apply_nvnv1_effect hierattrsdisabled largegrain outputsize ipaddress reversedescriptors s2fs1walk iswrite acctype vaddress secondstage inputaddr grainsize stride =
            (\<lambda> varstup . 
            (let (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) = varstup in
              (let addrselectbottom =
                ((((((( 3 :: int)::ii) - ((ex_int level)))) * ((ex_int stride))))
                  +
                  ((ex_int grainsize))) in
              liftR ((ZeroExtend_slice_append (( 52 :: int)::ii) inputaddr addrselectbottom
                        ((((((ex_int addrselecttop)) - ((ex_int addrselectbottom))))
                            +
                            (( 1 :: int)::ii))) (vec_of_bits [B0,B0,B0]  ::  3 Word.word)
                       :: ( 52 Word.word) M)) \<bind> (\<lambda> (index1 :: 52 bits) . 
              (let (tmp_210 :: FullAddress) = ((AddressDescriptor_paddress   descaddr)) in
              (let tmp_210 =
                ((tmp_210 (|
                  FullAddress_physicaladdress := ((or_vec baseaddress index1  ::  52 Word.word))|))) in
              (let descaddr = ((descaddr (| AddressDescriptor_paddress := tmp_210 |))) in
              (let (tmp_220 :: FullAddress) = ((AddressDescriptor_paddress   descaddr)) in
              (let tmp_220 = ((tmp_220 (| FullAddress_NS := ns_table |))) in
              (let descaddr = ((descaddr (| AddressDescriptor_paddress := tmp_220 |))) in
              or_boolM (return secondstage)
                (liftR (HasS2Translation () ) \<bind> (\<lambda> (w__143 :: bool) .  return ((\<not> w__143)))) \<bind> (\<lambda> (w__144 ::
                bool) . 
              (if w__144 then
                 (let (descaddr2 :: AddressDescriptor) = descaddr in
                 return (descaddr2, hwupdatewalk, result))
               else
                 (let hwupdatewalk = False in
                 liftR (AArch64_SecondStageWalk descaddr vaddress acctype iswrite (( 8 :: int)::ii)
                          hwupdatewalk) \<bind> (\<lambda> (w__145 :: AddressDescriptor) . 
                 (let descaddr2 = w__145 in
                 (if ((IsFault descaddr2)) then
                    (let (tmp_230 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                    (let tmp_230 =
                      ((tmp_230 (| AddressDescriptor_fault := ((AddressDescriptor_fault   descaddr2))|))) in
                    (let result = ((result (| TLBRecord_addrdesc := tmp_230 |))) in
                    (early_return result :: (unit, TLBRecord) MR) \<then> return result)))
                  else return result) \<bind> (\<lambda> (result :: TLBRecord) . 
                 return (descaddr2, hwupdatewalk, result)))))) \<bind> (\<lambda> varstup .  (let ((descaddr2 ::
                AddressDescriptor), (hwupdatewalk :: bool), (result :: TLBRecord)) = varstup in
              liftR ((ZeroExtend__1 (( 64 :: int)::ii) vaddress  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__146 :: 64 bits) . 
              (let descaddr2 = ((descaddr2 (| AddressDescriptor_vaddress := w__146 |))) in
              liftR (CreateAccessDescriptorPTW acctype secondstage s2fs1walk level) \<bind> (\<lambda> (w__147 ::
                AccessDescriptor) . 
              (let accdesc = w__147 in
              liftR ((aget__Mem descaddr2 (( 8 :: int)::ii) accdesc  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__148 :: 64
                bits) . 
              (let desc = w__148 in
              (if reversedescriptors then liftR ((BigEndianReverse desc  :: ( 64 Word.word) M))
               else return desc) \<bind> (\<lambda> (desc :: 64 bits) . 
              (if (((((((vec_of_bits [access_vec_dec desc (( 0 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B0]  ::  1 Word.word)))) \<or> ((((((((slice desc (( 0 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)))) \<and> (((((ex_int level)) = (( 3 :: int)::ii))))))))))
               then
                 (let (tmp_240 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                 liftR (AArch64_TranslationFault ipaddress level acctype iswrite secondstage
                          s2fs1walk) \<bind> (\<lambda> (w__150 :: FaultRecord) . 
                 (let tmp_240 = ((tmp_240 (| AddressDescriptor_fault := w__150 |))) in
                 (let result = ((result (| TLBRecord_addrdesc := tmp_240 |))) in
                 (early_return result :: (unit, TLBRecord) MR) \<then>
                 return (addrselecttop,
                         ap_table,
                         baseaddress,
                         blocktranslate,
                         level,
                         ns_table,
                         pxn_table,
                         result,
                         xn_table)))))
               else if ((((((((slice desc (( 0 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)))) \<or> (((((ex_int level)) = (( 3 :: int)::ii)))))))
               then
                 (let (blocktranslate :: bool) = True in
                 return (addrselecttop,
                         ap_table,
                         baseaddress,
                         blocktranslate,
                         level,
                         ns_table,
                         pxn_table,
                         result,
                         xn_table))
               else
                 or_boolM
                   (return ((((((((((ex_int outputsize)) < (( 52 :: int)::ii))) \<and> largegrain))) \<and> ((\<not> ((IsZero ((slice desc (( 12 :: int)::ii) (( 4 :: int)::ii)  ::  4 Word.word))))))))))
                   (and_boolM (return ((((ex_int outputsize)) < (( 48 :: int)::ii))))
                      (liftR (IsZero_slice desc outputsize
                                ((((- ((ex_int outputsize)))) + (( 48 :: int)::ii)))) \<bind> (\<lambda> (w__151 ::
                         bool) . 
                       return ((\<not> w__151))))) \<bind> (\<lambda> (w__153 :: bool) . 
                 if w__153 then
                   (let (tmp_250 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                   liftR (AArch64_AddressSizeFault ipaddress level acctype iswrite secondstage
                            s2fs1walk) \<bind> (\<lambda> (w__154 :: FaultRecord) . 
                   (let tmp_250 = ((tmp_250 (| AddressDescriptor_fault := w__154 |))) in
                   (let result = ((result (| TLBRecord_addrdesc := tmp_250 |))) in
                   (early_return result :: (unit, TLBRecord) MR) \<then>
                   return (addrselecttop,
                           ap_table,
                           baseaddress,
                           blocktranslate,
                           level,
                           ns_table,
                           pxn_table,
                           result,
                           xn_table)))))
                 else
                   (let gsz = grainsize in
                   liftR (assert_exp True ('''')) \<then>
                   ((let (baseaddress :: 52 bits) =
                     (if (((((ex_int outputsize)) = (( 52 :: int)::ii)))) then
                       (concat_vec ((slice desc (( 12 :: int)::ii) (( 4 :: int)::ii)  ::  4 Word.word))
                          ((slice_zeros_concat
                              ((((((- gsz)) + (( 48 :: int)::ii))) + gsz)) desc
                              gsz ((((- gsz)) + (( 48 :: int)::ii))) gsz
                             ::  48 Word.word))
                         ::  52 Word.word)
                     else
                       (place_slice (( 52 :: int)::ii) desc gsz ((((- gsz)) + (( 48 :: int)::ii)))
                          gsz
                         ::  52 Word.word)) in
                   (let (ns_table :: 1 bits) =
                     (if ((\<not> secondstage)) then
                       (or_vec ns_table (vec_of_bits [access_vec_dec desc (( 63 :: int)::ii)]  ::  1 Word.word)
                         ::  1 Word.word)
                     else ns_table) in
                   (let ((ap_table :: 2 bits), (pxn_table :: 1 bits), (xn_table :: 1 bits)) =
                     (if (((((\<not> secondstage)) \<and> ((\<not> hierattrsdisabled))))) then
                       (let (ap_table :: 2 bits) =
                         ((set_slice (( 2 :: int)::ii) (( 1 :: int)::ii) ap_table (( 1 :: int)::ii)
                            ((or_vec (vec_of_bits [access_vec_dec ap_table (( 1 :: int)::ii)]  ::  1 Word.word)
                                (vec_of_bits [access_vec_dec desc (( 62 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word))
                           ::  2 Word.word)) in
                       (let ((pxn_table :: 1 bits), (xn_table :: 1 bits)) =
                         (if apply_nvnv1_effect then
                           (let (pxn_table :: 1 bits) =
                             ((or_vec pxn_table
                                (vec_of_bits [access_vec_dec desc (( 60 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word)) in
                           (pxn_table, xn_table))
                         else
                           (let (xn_table :: 1 bits) =
                             ((or_vec xn_table
                                (vec_of_bits [access_vec_dec desc (( 60 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word)) in
                           (pxn_table, xn_table))) in
                       (let ((ap_table :: 2 bits), (pxn_table :: 1 bits)) =
                         (if ((\<not> singlepriv)) then
                           (let ((ap_table :: 2 bits), (pxn_table :: 1 bits)) =
                             (if ((\<not> apply_nvnv1_effect)) then
                               (let (pxn_table :: 1 bits) =
                                 ((or_vec pxn_table
                                    (vec_of_bits [access_vec_dec desc (( 59 :: int)::ii)]  ::  1 Word.word)
                                   ::  1 Word.word)) in
                               (let (ap_table :: 2 bits) =
                                 ((set_slice (( 2 :: int)::ii) (( 1 :: int)::ii) ap_table (( 0 :: int)::ii)
                                    ((or_vec
                                        (vec_of_bits [access_vec_dec ap_table (( 0 :: int)::ii)]  ::  1 Word.word)
                                        (vec_of_bits [access_vec_dec desc (( 61 :: int)::ii)]  ::  1 Word.word)
                                       ::  1 Word.word))
                                   ::  2 Word.word)) in
                               (ap_table, pxn_table)))
                             else (ap_table, pxn_table)) in
                           (ap_table, pxn_table))
                         else (ap_table, pxn_table)) in
                       (ap_table, pxn_table, xn_table))))
                     else (ap_table, pxn_table, xn_table)) in
                   (let (level :: ii) = (((ex_int level)) + (( 1 :: int)::ii)) in
                   (let (addrselecttop :: ii) = (((ex_int addrselectbottom)) - (( 1 :: int)::ii)) in
                   (let (blocktranslate :: bool) = False in
                   return (addrselecttop,
                           ap_table,
                           baseaddress,
                           blocktranslate,
                           level,
                           ns_table,
                           pxn_table,
                           result,
                           xn_table))))))))))) \<bind> (\<lambda> varstup .  (let ((addrselecttop :: ii), (ap_table :: 2
                bits), (baseaddress :: 52 bits), (blocktranslate :: bool), (level :: ii), (ns_table :: 1
                bits), (pxn_table :: 1 bits), (result :: TLBRecord), (xn_table :: 1 bits)) = varstup in
              return (accdesc,
                      addrselectbottom,
                      addrselecttop,
                      ap_table,
                      baseaddress,
                      blocktranslate,
                      desc,
                      descaddr,
                      descaddr2,
                      hwupdatewalk,
                      level,
                      ns_table,
                      pxn_table,
                      result,
                      xn_table)))))))))))))))))))))))"

definition
  "TranslationTableWalk_loop_cond =
            (\<lambda> varstup . 
            (let (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) = varstup in
              return blocktranslate))"

definition
  "TranslationTableWalk_loop_termination_precond vars =
     (case vars of (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) \<Rightarrow> level \<ge> 0 \<and> level < 4)"

definition
  "TranslationTableWalk_loop_variant vars =
     (case vars of (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) \<Rightarrow> 4 - nat level)"

definition calc_outputsize :: "3 word \<Rightarrow> bool \<Rightarrow> int" where
  "calc_outputsize PS largegrain =
     (if PS = vec_of_bits [B0, B0, B0] then 32
      else if PS = vec_of_bits [B0, B0, B1] then 36
      else if PS = vec_of_bits [B0, B1, B0] then 40
      else if PS = vec_of_bits [B0, B1, B1] then 42
      else if PS = vec_of_bits [B1, B0, B0] then 44
      else if PS = vec_of_bits [B1, B0, B1] then 48
      else if PS = vec_of_bits [B1, B1, B0] then if largegrain then 52 else 48 else 48)"

lemma calc_outputsize_bounds[simp]:
  "32 \<le> calc_outputsize PS largegrain" "calc_outputsize PS largegrain \<le> 52"
  "52 < calc_outputsize PS largegrain \<longleftrightarrow> False"
  by (auto simp: calc_outputsize_def)

definition Parameters_EL0 where
  "Parameters_EL0 descaddr secondstage top1 (inputaddr :: 64 word) c =
     (if ((((vec_of_bits [access_vec_dec inputaddr top1]  ::  1 Word.word) = (vec_of_bits [B0]  ::  1 Word.word)))) then
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__82 :: 64 bits) . 
        (let inputsize =
          ((( 64 :: int)::ii) - ((Word.uint ((slice w__82 (( 0 :: int)::ii) (( 6 :: int)::ii)  ::  6 Word.word))))) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__83 :: 64 bits) . 
        (let largegrain =
          (((slice w__83 (( 14 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__84 :: 64 bits) . 
        (let midgrain =
          (((slice w__84 (( 14 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B1,B0]  ::  2 Word.word)) in
        (let inputsize_max =
          (if (((((Have52BitVAExt () )) \<and> largegrain))) then (( 52 :: int)::ii)
          else (( 48 :: int)::ii)) in
        (if ((((ex_int inputsize)) > ((ex_int inputsize_max)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_max
             else inputsize) in
           return (c, inputsize))))
         else return (c, inputsize)) \<bind> (\<lambda> varstup .  (let ((c :: Constraint), (inputsize ::
          ii)) = varstup in
        (let inputsize_min = ((( 64 :: int)::ii) - (( 39 :: int)::ii)) in
        (if ((((ex_int inputsize)) < ((ex_int inputsize_min)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_min
             else inputsize) in
           return inputsize)))
         else return inputsize) \<bind> (\<lambda> (inputsize :: ii) . 
        and_boolM
          (return (((((((ex_int inputsize)) \<ge> ((ex_int inputsize_min)))) \<and> ((((ex_int inputsize)) \<le> ((ex_int inputsize_max))))))))
          (liftR ((IsZero_slice inputaddr inputsize
                     ((((((ex_int top1)) - ((ex_int inputsize)))) +
                         (( 1 :: int)::ii)))))) \<bind> (\<lambda> (w__86 :: bool) . 
        (let basefound = w__86 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__87 :: 64 bits) . 
        (let disabled =
          ((vec_of_bits [access_vec_dec w__87 (( 7 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)) in
        liftR ((read_reg TTBR0_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__88 :: 64 bits) . 
        (let baseregister = w__88 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__89 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__90 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__91 :: 64 bits) . 
        liftR (WalkAttrDecode ((slice w__89 (( 12 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__90 (( 10 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__91 (( 8 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) secondstage) \<bind> (\<lambda> (w__92 ::
          MemoryAttributes) . 
        (let descaddr = ((descaddr (| AddressDescriptor_memattrs := w__92 |))) in
        and_boolM (return ((AArch64_HaveHPDExt () )))
          (liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__93 :: 64 bits) . 
           return ((((vec_of_bits [access_vec_dec w__93 (( 41 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)))))) \<bind> (\<lambda> (w__94 :: bool) . 
        (let (hierattrsdisabled :: bool) = w__94 in
        return (basefound,
                baseregister,
                descaddr,
                disabled,
                hierattrsdisabled,
                inputsize,
                largegrain,
                midgrain)))))))))))))))))))))))))
      else
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__95 :: 64 bits) . 
        (let inputsize =
          ((( 64 :: int)::ii) - ((Word.uint ((slice w__95 (( 16 :: int)::ii) (( 6 :: int)::ii)  ::  6 Word.word))))) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__96 :: 64 bits) . 
        (let largegrain =
          (((slice w__96 (( 30 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B1,B1]  ::  2 Word.word)) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__97 :: 64 bits) . 
        (let midgrain =
          (((slice w__97 (( 30 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)) in
        (let inputsize_max =
          (if (((((Have52BitVAExt () )) \<and> largegrain))) then (( 52 :: int)::ii)
          else (( 48 :: int)::ii)) in
        (if ((((ex_int inputsize)) > ((ex_int inputsize_max)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_max
             else inputsize) in
           return (c, inputsize))))
         else return (c, inputsize)) \<bind> (\<lambda> varstup .  (let ((c :: Constraint), (inputsize ::
          ii)) = varstup in
        (let inputsize_min = ((( 64 :: int)::ii) - (( 39 :: int)::ii)) in
        (if ((((ex_int inputsize)) < ((ex_int inputsize_min)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_min
             else inputsize) in
           return inputsize)))
         else return inputsize) \<bind> (\<lambda> (inputsize :: ii) . 
        and_boolM
          (return (((((((ex_int inputsize)) \<ge> ((ex_int inputsize_min)))) \<and> ((((ex_int inputsize)) \<le> ((ex_int inputsize_max))))))))
          (liftR ((IsOnes_slice inputaddr inputsize
                     ((((((ex_int top1)) - ((ex_int inputsize)))) +
                         (( 1 :: int)::ii)))))) \<bind> (\<lambda> (w__99 :: bool) . 
        (let basefound = w__99 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__100 :: 64 bits) . 
        (let disabled =
          ((vec_of_bits [access_vec_dec w__100 (( 23 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)) in
        liftR ((read_reg TTBR1_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__101 :: 64 bits) . 
        (let baseregister = w__101 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__102 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__103 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__104 :: 64 bits) . 
        liftR (WalkAttrDecode ((slice w__102 (( 28 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__103 (( 26 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__104 (( 24 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) secondstage) \<bind> (\<lambda> (w__105 ::
          MemoryAttributes) . 
        (let descaddr = ((descaddr (| AddressDescriptor_memattrs := w__105 |))) in
        and_boolM (return ((AArch64_HaveHPDExt () )))
          (liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__106 :: 64 bits) . 
           return ((((vec_of_bits [access_vec_dec w__106 (( 42 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)))))) \<bind> (\<lambda> (w__107 :: bool) . 
        (let (hierattrsdisabled :: bool) = w__107 in
        return (basefound,
                baseregister,
                descaddr,
                disabled,
                hierattrsdisabled,
                inputsize,
                largegrain,
                midgrain))))))))))))))))))))))))))"

definition calc_startlevel where
  "calc_startlevel inputsize grainsize stride \<equiv>
     ((( 4 :: int)::ii) -
                  ((ex_int
                      ((ceiling
                          (((((real_of_int ((((ex_int inputsize)) - ((ex_int grainsize)))))))
                              div
                              (((real_of_int stride))))))))))"

definition calc_baseaddress where
  "calc_baseaddress baseregister baselowerbound outputsize \<equiv>
     (if (((((ex_int outputsize)) = (( 52 :: int)::ii)))) then
        (let z = (if ((baselowerbound < (( 6 :: int)::ii))) then (( 6 :: int)::ii) else baselowerbound) in
        liftR (assert_exp True ('''')) \<then>
        ((let (baseaddress :: 52 bits) =
          ((concat_vec ((slice baseregister (( 2 :: int)::ii) (( 4 :: int)::ii)  ::  4 Word.word))
             ((slice_zeros_concat ((((((- z)) + (( 48 :: int)::ii))) + z))
                 baseregister z ((((- z)) + (( 48 :: int)::ii))) z
                ::  48 Word.word))
            ::  52 Word.word)) in
        return baseaddress)))
      else
        (let (baseaddress :: 52 bits) =
          ((place_slice (( 52 :: int)::ii) baseregister baselowerbound
             ((((- baselowerbound)) + (( 48 :: int)::ii))) baselowerbound
            ::  52 Word.word)) in
        return baseaddress))"

definition calc_firstblocklevel_grainsize where
  "calc_firstblocklevel_grainsize largegrain midgrain \<equiv>
     (if largegrain then
       (let (grainsize :: ii) = ((( 16 :: int)::ii)) in
       (let (firstblocklevel :: ii) = (if ((Have52BitPAExt () )) then (( 1 :: int)::ii) else (( 2 :: int)::ii)) in
       (firstblocklevel, grainsize)))
     else
       (let ((firstblocklevel :: ii), (grainsize :: ii)) =
         (if midgrain then
           (let (grainsize :: ii) = ((( 14 :: int)::ii)) in
           (let (firstblocklevel :: ii) = ((( 2 :: int)::ii)) in
           (firstblocklevel, grainsize)))
         else
           (let (grainsize :: ii) = ((( 12 :: int)::ii)) in
           (let (firstblocklevel :: ii) = ((( 1 :: int)::ii)) in
           (firstblocklevel, grainsize)))) in
       (firstblocklevel, grainsize)))"

definition calc_contiguousbitcheck where
  "calc_contiguousbitcheck inputsize largegrain midgrain level \<equiv>
     (if largegrain then ex_int level = 2 \<and> ex_int inputsize < 34
      else if midgrain then ex_int level = 2 \<and> ex_int inputsize < 30
      else ex_int level = 1 \<and> ex_int inputsize < 34)"

end
