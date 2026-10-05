import Mathlib


namespace first_isomorphism_theorem

section Grupos

variable {G : Type} [Group G]

#check mul_assoc
#check one_mul
#check mul_one

theorem retirar_identidades (a b : G) : (1 * a) * (b * 1) = a * b := by
  rw [one_mul]
  rw [mul_one]


theorem reassociar (a b c d : G) :
    ((a * b) * c) * d = a * (b * (c * d)) := by
  rw [mul_assoc]
  rw [mul_assoc]

theorem substituir_ao_contrario (a b c : G) (h : a = b) :
    b * c = a * c := by
  rw [<-h]

theorem reorganizar_com_calc (a b c : G) :
    (a * 1) * (b * c) = (a * b) * c := by
  calc
    (a * 1) * (b * c) = a * (b * c) := by rw [mul_one]
    _ = (a * b) * c := by rw [mul_assoc]

#check congrArg

theorem multiplicar_a_esquerda (a b c : G) (h : b = c) :
    a * b = a * c := by
  exact congrArg (fun x => a * x) h

theorem cancelar_a_esquerda (a b c : G)
    (h : a * b = a * c) : b = c := by
    have h' := congrArg (fun x => a⁻¹ * x) h
    rw [<-mul_assoc] at h'
    rw [<-mul_assoc] at h'
    rw [inv_mul_cancel] at h'
    rw [one_mul] at h'
    rw [one_mul] at h'
    exact h'

theorem cancelar_a_direita (a b c : G)
    (h : b * a = c * a) : b = c := by
  have h' := congrArg (fun x => x * a⁻¹) h
  rw [mul_assoc] at h'
  rw [mul_assoc] at h'
  rw [mul_inv_cancel] at h'
  rw [mul_one] at h'
  rw [mul_one] at h'
  exact h'

end Grupos

section Homomorfismos

variable {G H : Type} [Group G] [Group H]

-- G →* H é o tipo dos homomorfismos multiplicativos

example (f : G →* H) (a b : G) : f (a * b) = f a * f b := by
  exact f.map_mul a b

#check (fun (f : G →* H) => f.map_one)

theorem imagem_produto_triplo (f : G →* H) (a b c : G) :
    f ((a * b) * c) = (f a * f b) * f c := by
  have h1 := (f.map_mul (a * b) c)
  have h2 := f.map_mul a b
  rw [h2] at h1
  exact h1

theorem produto_com_imagem_um (f : G →* H) (a b : G)
    (ha : f a = 1) (hb : f b = 1) :
    f (a * b) = 1 := by
  have h1 := f.map_mul a b
  rw [ha,hb] at h1
  rw [one_mul] at h1
  exact h1

theorem imagem_inverso (f : G →* H) (a : G) :
    f (a⁻¹) = (f a)⁻¹ := by
  have h1 := f.map_mul a⁻¹ a
  rw [inv_mul_cancel] at h1
  rw [f.map_one] at h1
  have h2 := inv_mul_cancel (f a)
  rw [<-h2] at h1
  apply cancelar_a_direita at h1
  symm at h1
  exact h1

theorem inverso_com_imagem_um (f : G →* H) (a : G)
    (ha : f a = 1) : f (a⁻¹) = 1 := by
  rw [imagem_inverso f a]
  rw [ha]
  exact inv_one

def nucleo (f : G →* H) : Subgroup G where
  carrier := {a : G | f a = 1}
  one_mem' := by
    exact f.map_one
  mul_mem' := by
    intro a b ha hb
    exact produto_com_imagem_um f a b ha hb
  inv_mem' := by
    intro a ha
    exact inverso_com_imagem_um f a ha

def imagem (f : G →* H) : Subgroup H where
  carrier := {b : H | ∃ a : G, f a = b}
  one_mem' := by
    use 1
    exact f.map_one
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    -- f a = x * y
    change ∃ a, f a = x * y
    use (a*b)
    rw [f.map_mul a b]
    rw [ha]
    rw [hb]
  inv_mem' := by
    intro x hx
    change ∃ a, f a = x⁻¹
    change ∃ a, f a = x at hx
    rcases hx with ⟨a, ha⟩
    use a⁻¹
    rw [imagem_inverso]
    rw [ha]

#check imagem

theorem conjugacao_com_imagem_um (f : G →* H)
    (g k : G) (hk : f k = 1) :
    f (g * k * g⁻¹) = 1 := by
  rw [mul_assoc]
  rw [f.map_mul (g) (k * g⁻¹)]
  rw [f.map_mul k g⁻¹]
  rw [hk]
  rw[one_mul]
  rw [imagem_inverso]
  rw [mul_inv_cancel (f g)]


instance (f : G →* H) : Subgroup.Normal (nucleo f) where
  conj_mem := by
    intro h y g
    change f (g * h * g⁻¹) = 1
    change f h = 1 at y
    apply conjugacao_com_imagem_um
    exact y


theorem mem_nucleo_iff_imagem_igual (a b : G) (f : G →* H) :
  a⁻¹ * b ∈ (nucleo f) ↔ f (a) = f (b) := by
  change f (a⁻¹ * b) = 1 ↔ f a = f b
  constructor
  case mp =>
    intro h
    rw [f.map_mul a⁻¹ b] at h
    rw [imagem_inverso] at h
    have h' := congrArg (fun x => f a * x) h
    rw [<-mul_assoc] at h'
    rw [mul_inv_cancel (f a)] at h'
    rw [one_mul, mul_one] at h'
    symm
    exact h'
  case mpr =>
    intro h
    rw [f.map_mul a⁻¹ b]
    rw [<-h]
    rw [imagem_inverso]
    rw [inv_mul_cancel (f a)]

def relacao (f : G →* H) (a b : G) : Prop :=
  a⁻¹ * b ∈ nucleo f

#check (fun (f : G →* H) (a b : G) => relacao f a b)

def meu_setoid (f : G →* H) : Setoid G where
  r := relacao f
  iseqv := {
    refl := by
      intro a
      change a⁻¹ * a ∈ nucleo f
      change f (a⁻¹ * a) = 1
      rw [inv_mul_cancel]
      rw [f.map_one]
    symm := by
      intro a b hp
      change a⁻¹ * b ∈ nucleo f at hp
      change b⁻¹ * a ∈ nucleo f
      change f (a⁻¹ * b) = 1 at hp
      change f (b⁻¹ * a) = 1
      rw [f.map_mul] at hp
      rw [f.map_mul]
      rw [imagem_inverso] at hp
      rw [imagem_inverso]
      have h' := congrArg (fun x => f a * x) hp
      rw [<-mul_assoc] at h'
      rw [mul_inv_cancel] at h'
      rw [one_mul] at h'
      have h'' := congrArg (fun x => f b⁻¹ * x) h'
      rw [imagem_inverso] at h''
      rw [inv_mul_cancel] at h''
      rw [mul_one] at h''
      symm
      exact h''
    trans := by
      intro x y z hpxy hpyz
      change x⁻¹ * y ∈ nucleo f at hpxy
      change y⁻¹ * z ∈ nucleo f at hpyz
      change x⁻¹ * z ∈ nucleo f
      change f (x⁻¹ * y) = 1 at hpxy
      change f (y⁻¹ * z) = 1 at hpyz
      change f (x⁻¹ * z) = 1
      rw [f.map_mul] at hpxy
      rw [f.map_mul] at hpyz
      rw [f.map_mul]
      rw [imagem_inverso] at hpxy
      rw [imagem_inverso] at hpyz
      rw [imagem_inverso]
      have h' := congrArg (fun d => d * (f y)⁻¹) hpxy
      rw [mul_assoc] at h'
      rw [mul_inv_cancel] at h'
      rw [one_mul, mul_one] at h'
      have h'' := congrArg (fun d => d * f z) h'
      rw [hpyz] at h''
      exact h''
  }


#check Quotient
#check Quotient.mk
#check fun (f : G →* H) (a : G) => Quotient.mk (meu_setoid (f: G →* H)) (a : G)


def quociente (f : G →* H) : Type := Quotient (meu_setoid f)

#check quociente

#check (fun (f : G →* H) (a b : G) => relacao f a b)

def projecao_representante (f : G →* H) (a : G) : quociente f := Quotient.mk (meu_setoid f) a

#check projecao_representante



def mapa_induzido (f : G →* H) : quociente f → H :=
  Quotient.lift (fun a => f a) (by
    intro a b hab
    exact (mem_nucleo_iff_imagem_igual a b f).mp hab)

theorem mapa_induzido_aplica_classe (f : G →* H) :
∀ (a : G), (mapa_induzido f) (projecao_representante f a) = f a :=
  by
    intro x
    rfl

theorem classes_iguais_de_imagens_iguais (a b : G) (f : G →* H) :
(mapa_induzido f) (projecao_representante f a) = (mapa_induzido f) (projecao_representante f b) →
(projecao_representante f a) = (projecao_representante f b) := by
  intro hp
  rw [mapa_induzido_aplica_classe] at hp
  rw [mapa_induzido_aplica_classe] at hp
  apply Quotient.sound
  change a⁻¹ * b ∈ nucleo f
  exact (mem_nucleo_iff_imagem_igual a b f).mpr hp

theorem teste (f : G →* H) : Function.Injective (mapa_induzido f) := by
  intro q1 q2 hp
  apply Quotient.inductionOn
  intro a
  -- apply [classes_iguais_de_imagens_iguais] at hp
  sorry

def valor_na_imagem (f : G →* H) (a : G) : imagem f := by
  refine ⟨f a, ?_⟩
  change ∃ b : G, f b = f a
  use a

-- #check (fun (f : G →* H) (a b : G) => valor_na_imagem f a).val
-- #check (valor_na_imagem f a).property

theorem valor_na_imagem_igual (f : G →* H) (a : G) : valor_na_imagem f a = f a := by
  rfl

theorem sobrejetividade (f : G →* H) (y : imagem f) : ∃ (a : G), (valor_na_imagem f a) = y := by
  have teste := y.property
  change ∃ b : G, f b = y at teste
  rcases teste with ⟨x, h⟩
  use x
  apply Subtype.ext
  rw [valor_na_imagem]
  exact h

theorem representante_escolha_nao_importa (f : G →* H) (a b : G) : relacao f a b → valor_na_imagem f a = valor_na_imagem f b := by
  intro hfab
  change a⁻¹ * b ∈ nucleo f at hfab
  change f (a⁻¹ * b) = 1 at hfab
  have lema1 := valor_na_imagem_igual f a
  have lema2 := valor_na_imagem_igual f b
  apply Subtype.ext
  rw [lema1,lema2]
  rw [f.map_mul] at hfab
  have lema3 := congrArg (fun x => (f a) * x) hfab
  rw [<-mul_assoc] at lema3
  rw [imagem_inverso] at lema3
  rw [mul_inv_cancel] at lema3
  rw [one_mul, mul_one] at lema3
  symm
  exact lema3


#check (fun (f : G →* H) (a b : G) => relacao f a b)



#check Quotient.inductionOn

--def valor_imagem_mapa_induzido (f : G →* H) (a : G) := { f a : H // f a ∈ imagem }

-- eu n entendi mt bem o que eu tava fznd com o quociente. vale a pena revisar
-- o que Quotient faz, o que Quotient.mk faz, o que Quotient.lift faz e essas coisas


def mod_2 (a b : Int) : Prop :=
  a % 2 = b % 2


def mod_2_setoid : Setoid ℤ where
  r := mod_2
  iseqv := {
    refl := by
      intro x
      change x % 2 = x % 2
      rfl
    symm := by
      intro x y hp
      change x % 2 = y % 2 at hp
      change y % 2 = x % 2
      symm
      exact hp
    trans := by
      intro x y z hp1 hp2
      change x % 2 = y % 2 at hp1
      change y % 2 = z % 2 at hp2
      change x % 2 = z % 2
      rw [hp1,hp2]
  }

def mod_2_quociente : Type := Quotient mod_2_setoid

def mod_2_quociente_representante (a : Int) : mod_2_quociente := Quotient.mk mod_2_setoid a

#check mod_2_quociente_representante 2

theorem zero_is_dois : mod_2_quociente_representante 0 = mod_2_quociente_representante 2 := by
  apply Quotient.sound
  change 0 % 2 = 2 % 2
  rfl

theorem zero_is_not_one : ¬(mod_2_quociente_representante 0 = mod_2_quociente_representante 1) := by
  intro hp
  have hrel := Quotient.exact hp
  change 0 % 2 = 1 % 2 at hrel
  simp at hrel

theorem all_class_equal_zero_or_one :
  ∀ (a : ℤ ), mod_2_quociente_representante a = mod_2_quociente_representante 0 ∨ mod_2_quociente_representante a = mod_2_quociente_representante 1 :=
  sorry

def soma_mod_2 (a b : Int) : Int :=
  a + b % 2

#eval soma_mod_2 3 2


#eval 3 % 2 == 0

#eval 3 % 2 == 5 % 2

#check mod_2 3 2


end Homomorfismos

#check Subgroup.Normal


end first_isomorphism_theorem
