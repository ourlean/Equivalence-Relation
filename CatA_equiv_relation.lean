/- by Li Xiang, Laraia Thomas, Pratt Johns Joe, Yu Ella -/
/- GNU General Public License v3.0 -/

import tactic
noncomputable theory

/- 1 Basic Definitions-/

/- There are two ways to define the equivalence relation -/
/- Approach I: Set Theory-/

def is_refl_set {X:Type}(S: set (X× X)):=
∀ a: X, (a,a)∈ S

def is_symm_set {X:Type}(S: set (X× X)):=
∀ a b:X, (a,b)∈ S→ (b,a)∈S 

def is_trans_set {X:Type}(S:set (X× X)):=
∀ a b c:X, (a,b)∈ S→ (b,c)∈ S→ (a,c)∈ S 

def is_equiv_set {X:Type}(S:set (X× X)):=
is_refl_set S ∧ is_symm_set S 
∧ is_trans_set S

def equiv_class_set {X:Type}(S:set (X× X))(a:X):=
{x:X | (x,a)∈ S}

def quotient_set {X:Type}(S:set (X× X)):=
{e:set X | ∃ a:X, e=equiv_class_set S a}

/- Approach II: Type Theory-/
/- I will use this approach in the follwing files. -/

def is_refl_type {X:Type}(S: X→ X→ Prop):= -- Def 1 --
∀ a:X, S a a

def is_symm_type {X:Type}(S: X→ X→ Prop):= -- Def 2 --
∀ a b:X, S a b→ S b a

def is_trans_type {X:Type}(S:X→ X→ Prop):= -- Def 3 --
∀ a b c:X, S a b→ S b c→ S a c 

def is_equiv_type {X:Type}(S:X→ X→ Prop):= -- Def 4--
is_refl_type S ∧ is_symm_type S 
∧ is_trans_type S

def equiv_class_type {X:Type}(S:X→ X→ Prop)(a:X):= -- Def 5 --
{x:X | S x a}

def quotient_type {X:Type}(S:X→ X→ Prop):= --Def 6 --
{e:set X | ∃ a:X, e=equiv_class_type S a}

/- 2 Properties -/

def convert_to_set(X:Type):set X:={x:X | true}

lemma in_equiv_class {X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X):
a∈ equiv_class_type S a:= -- Lemma 7 --
begin
  cases h with p q,
  apply p a,
end

lemma equiv_class_is_subset{X:Type}(S:X→ X→ Prop)(a:X):
(equiv_class_type S a)⊆convert_to_set(X)
:= -- Lemma 8 --
begin
  intros x f,
  rw convert_to_set,
  rw set.mem_set_of_eq,
  cc,
end

lemma equiv_iff_same_class {X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X)(b:X):
S a b ↔ equiv_class_type S a=equiv_class_type S b
:=  -- Lemma 9 --
begin
  have rfl:=h.1,
  have sym:=h.2.1,
  have tran:=h.2.2,
  split,

  /- → -/
  intro f,
  --cases h with rfl st,
  --cases st with sym tran,
  rw set.subset.antisymm_iff,
  split,
  /- → ⊆-/
  intros x g,
  apply tran x a b g f,
  /- → ⊇ -/
  intros x g,
  have t:=sym a b f,
  apply tran x b a g t,

  /- ← -/
  intro f,
  have u:=in_equiv_class h a,
  rw f at u,
  exact u,
end

lemma equiv_iff_class_intersect{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X)(b:X):
S a b ↔ (equiv_class_type S a ∩ equiv_class_type S b).nonempty
:= --Lemma 10 --
begin
  have rfl:=h.1,
  have sym:=h.2.1,
  have tran:=h.2.2,
  split,

  /- → -/
  intro f,
  rw set.nonempty,
  use a,
  rw set.mem_inter_eq,
  split,
  have t:=in_equiv_class h a,
  exact t,
  exact f,

  /- ← -/
  intro f,
  cases f with x fx,
  rw set.mem_inter_eq at fx,
  cases fx with fxp fxq,
  have t:=sym x a fxp,
  apply tran a x b t fxq,
end 

lemma same_class_iff_intersect{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X)(b:X): -- Lemma 11 --
equiv_class_type S a = equiv_class_type S b ↔ 
(equiv_class_type S a ∩ equiv_class_type S b).nonempty:=
begin
  have p:=equiv_iff_same_class h a b,
  have q:=equiv_iff_class_intersect h a b,
  rw p at q,
  exact q,
end 

lemma contrapose_iff {P:Prop}{Q:Prop}:(P↔Q)↔(¬P↔¬Q):=
begin
  split,
  intro f,
  cc,
  intro f,
  split,
  cc,
  cc,
end

lemma equiv_class_disjoint{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X)(b:X):
equiv_class_type S a ≠ equiv_class_type S b ↔ 
(equiv_class_type S a ∩ equiv_class_type S b)=∅ 
:= -- Lemma 12 --
begin
  have q:=same_class_iff_intersect h a b,
  rw contrapose_iff at q,
  rw set.not_nonempty_iff_eq_empty at q,
  cc,
end

lemma equiv_class_union{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S):
(⋃ (ind:X), (equiv_class_type S ind))=convert_to_set(X)
:= -- Lemma 13 --
begin
  rw set.subset.antisymm_iff,
  split,
  
  /- ⊆ -/
  intros x f,
  rw convert_to_set,
  rw set.mem_set_of_eq,
  cc,

  /- ⊇ -/
  intros x f,
  have t:=in_equiv_class h x,
  rw set.mem_Union,
  use x,
  exact t,
end

/- 3 Canonical Map and Section -/

lemma equiv_class_type_in_quotient_type{X:Type}
(S:X→ X→ Prop)(a:X): 
equiv_class_type S a ∈ quotient_type S:= -- Lemma 14 --
begin
  use a,
end

def can{X:Type}(S:X→ X→ Prop):X→ quotient_type S:= -- Def 15 --
λa,⟨equiv_class_type S a, equiv_class_type_in_quotient_type S a⟩

lemma in_can{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X):
a∈ (can S a).val:=
begin
  exact in_equiv_class h a,
end

lemma can_be_repres{X:Type}{S:X→ X→ Prop}
(e:quotient_type S):∃ a:X, e.val=equiv_class_type S a
:= -- Lemma 16 pre --
begin
  have t:=subtype.mem e,
  cases t with a ta,
  use a,
  exact ta,
end

lemma equiv_class_nonempty{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(e:quotient_type S):e.val.nonempty
:= -- Lemma 16 --
begin
  rw set.nonempty_def,
  have t:=can_be_repres e,
  cases t with a ta,
  use a,
  rw ta,
  apply in_equiv_class h a,  
end

def particular_sec{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S):quotient_type S→ X:= -- Def 17 --
λe, set.nonempty.some (equiv_class_nonempty h e)

def can_sec{X:Type}{S:X→ X→ Prop}(sec:(quotient_type S)→ X):
quotient_type S→ quotient_type S := -- Def 18 --
λe, can S (sec e)

lemma sec_equiv{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S)
{sec:(quotient_type S)→ X}{sec':(quotient_type S)→ X}
(hs: can_sec sec=id)(hs': can_sec sec'=id)(e:quotient_type S):
S (sec e) (sec' e):= -- Lemma 19 --
begin
  rw equiv_iff_same_class h,
  unfold can_sec at *,
  have t:=(congr_fun (eq.symm hs) e).symm,
  have u:=(congr_fun (eq.symm hs') e).symm,
  unfold can at *,
  rw ← t at u,
  simp at *,
  symmetry,
  exact u,
end

lemma par_sec_in{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S)
(x:quotient_type S):
(particular_sec h x) ∈ x.val:= -- Lemma 20 --
begin
  unfold particular_sec,
  exact (equiv_class_nonempty h x).some_mem,
end

@[simp] lemma can_par_sec_id{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S):
can_sec (particular_sec h)=id:= -- Lemma 21 --
begin
  unfold can_sec,
  ext1,
  unfold id,
  ext1,
  unfold can,
  simp,
  have t:=in_equiv_class h (particular_sec h x),
  have u:=par_sec_in h x,
  have v:∃a:X, x.val=equiv_class_type S a:=can_be_repres x,
  cases v with a,
  simp at *,
  rw v_h at *,
  have ne_empty:((equiv_class_type S (particular_sec h x))∩ 
  (equiv_class_type S a)).nonempty:=begin
    rw set.nonempty_def,
    use particular_sec h x,
    simp,
    split,
    exact t,
    exact u,
  end,
  rw same_class_iff_intersect h _ _,
  exact ne_empty,
end

@[simp] lemma can_par_sec{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(e:quotient_type S):
can_sec (particular_sec h) e=e:= -- Lemma 21' --
begin
  rw can_par_sec_id,
  rwa id,
end

@[simp] lemma can_par_sec_expand{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(e:quotient_type S):
can S (particular_sec h e)=e:= -- Lemma 21'' --
begin
  have t:can S(particular_sec h e)=can_sec (particular_sec h) e:=
    by unfold can_sec,
  rw t,
  exact can_par_sec h e,
end

lemma par_sec_can{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X):
S (particular_sec h (can S a)) a:= -- Lemma 22 --
begin
  have t:=par_sec_in h (can S a),
  unfold can at t,
  unfold equiv_class_type at t,
  simp at *,
  exact t,
end

lemma equiv_iff_same_image_under_can{X:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(a:X)(b:X):
S a b ↔ can S a=can S b:= -- Lemma 23 --
begin
  unfold can,
  simp,
  exact equiv_iff_same_class h a b,
end

/- 4 Operations -/

def induced_op_by_sec{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(sec:(quotient_type S)→ X)(op:X→ Y):
quotient_type S→ Y:= -- Def 24, one argument --
λ e, op (sec e)

def induced_op{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(op:X→ Y):= -- Def 25, one argument --
induced_op_by_sec h (particular_sec h) op

def op_is_well_defined{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(op:X→ Y):= -- Def 26, one argument --
∀ a b:X, S a b → op a=op b 

lemma op_reduction{X:Type}{Y:Type}{S:X→ X→ Prop}
{h: is_equiv_type S}{op:X→ Y}
(hw: op_is_well_defined h op)
{e :quotient_type S}{a:X}{c:Y}
(h1: can S a=e)(ho: op a=c):
induced_op h op e=c:= -- Lemma 27, one argument --
begin
  unfold induced_op,
  unfold induced_op_by_sec,
  rw ← h1,
  have t:=par_sec_can h a,
  have u:=hw _ _ t,
  rw u,
  exact ho,
end

def induced_op2_by_sec{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(sec:(quotient_type S)→ X)(op:X→ X→ Y):
quotient_type S→ quotient_type S→ Y:= -- Def 24', two arguments --
λe1,λe2, op (sec e1) (sec e2)

def induced_op2{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(op:X→ X→ Y):= -- Def 25', two arguments --
induced_op2_by_sec h (particular_sec h) op

def op2_is_well_defined{X:Type}{Y:Type}{S:X→ X→ Prop}
(h: is_equiv_type S)(op:X→ X→ Y):= -- Def 26', two arguments --
∀ a b c d:X, S a c→ S b d→ op a b=op c d 

lemma op2_reduction{X:Type}{Y:Type}{S:X→ X→ Prop}
{h: is_equiv_type S}{op:X→ X→ Y}
(hw: op2_is_well_defined h op)
{e1 e2 :quotient_type S}{a b:X}{c:Y}
(h1: can S a=e1)(h2:can S b=e2)(ho: op a b=c):
induced_op2 h op e1 e2=c:= -- Lemma 27', two arguments --
begin
  unfold induced_op2,
  unfold induced_op2_by_sec,
  rw ← h1,
  rw ← h2,
  have t1:=par_sec_can h a,
  have t2:=par_sec_can h b,
  have u:=hw _ _ _ _ t1 t2,
  rw u,
  exact ho,
end

/- 5 Partition -/

lemma Enonempty{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S):
∀ e∈ quotient_type S, (e:set X).nonempty:=
begin
  intros e f,
  unfold quotient_type at f,
  simp at *,
  cases f with a,
  use a,
  rw f_h,
  exact in_equiv_class h a,
end

lemma Ecover{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S):
∀ a:X, ∃ e ∈ quotient_type S, a ∈ e:=
begin
  intro a,
  use (equiv_class_type S a),
  split,
  exact equiv_class_type_in_quotient_type _ _,
  exact in_equiv_class h a,
end

lemma Edisjoint{X:Type}{S:X→ X→ Prop}(h: is_equiv_type S):
∀ e1 e2 ∈ quotient_type S, (e1 ∩ e2 : set X).nonempty → e1=e2:=
begin
  intros e1 e2 f g s,
  unfold quotient_type at *,
  simp at *,
  cases f with a,
  cases g with b,
  rw f_h at *,
  rw g_h at *,
  rw (same_class_iff_intersect h a b),
  exact s,
end
