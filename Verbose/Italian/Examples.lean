import Verbose.Italian.ExampleLib

Exercise "Continuità implica continuità sequenziale"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u tende a x₀) (hf : f è continua in x₀)
  Conclusion: (f ∘ u) tende a f x₀
Proof:
  Dimostriamo che ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sia ε > 0
  Per hf applicato a ε usando ε > 0 otteniamo δ tale che (δ_pos : δ > 0) e (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Per hu applicato a δ usando δ > 0 otteniamo N tale che Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Dimostriamo che N funziona : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sia n ≥ N
  Per Hf applicato a u n è sufficiente dimostrare |u n - x₀| ≤ δ
  Noi concludiamo per Hu applicato a n usando n ≥ N
QED

-- Variation without referring to any assumption label
Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u tende a x₀) (hf : f è continua in x₀)
  Conclusion: (f ∘ u) tende a f x₀
Proof:
  Dimostriamo che ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sia ε > 0
  Since f è continua in x₀ and ε > 0 otteniamo δ tale che
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Since u tende a x₀ and δ > 0 otteniamo N tale che Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Dimostriamo che N funziona : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sia n ≥ N
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε è sufficiente dimostrare that |u n - x₀| ≤ δ
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we conclude that |u n - x₀| ≤ δ
  /- -- Forward reasoning variation
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N otteniamo h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ we conclude that |f (u n) - f x₀| ≤ ε -/
QED

Example "Constant sequences converge."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (h : ∀ n, u n = l)
  Conclusion: u tende a l
Proof:
  Sia ε > 0
  Dimostriamo che ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Dimostriamo che 0 funziona
  Sia n ≥ 0
  Calc |u n - l| = |l - l| by We rewrite usando h
   _             = 0       by We compute
   _             ≤ ε       by Noi concludiamo per ε_pos
QED

Example "A sequence converging to a positive limit is ultimately positive."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (hl : l > 0) (h :u tende a l)
  Conclusion: ∃ N, ∀ n ≥ N, u n ≥ l/2
Proof:
  Per h applicato a l/2 usando that l/2 > 0 otteniamo N tale che hN : ∀ n ≥ N, |u n - l| ≤ l/2
  Dimostriamo che N funziona
  Sia n ≥ N
  Per hN applicato a n usando that n ≥ N otteniamo hN' : |u n - l| ≤ l/2
  Per hN' otteniamo (h₁ : -(l/2) ≤ u n - l) (h₂ : u n - l ≤ l/2)
  Noi concludiamo per h₁
QED


Example "Addition of convergent sequences."
  Given: (u v : ℕ → ℝ) (l l' : ℝ)
  Assume: (hu : u tende a l) (hv : v tende a l')
  Conclusion: (u + v) tende a (l + l')
Proof:
  Sia ε > 0
  Per hu applicato a ε/2 usando that ε/2 > 0 otteniamo N₁
      tale che (hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε / 2)
  Per hv applicato a ε/2 usando that ε/2 > 0 otteniamo N₂
      tale che (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Dimostriamo che max N₁ N₂ funziona
  Sia n ≥ max N₁ N₂
  Per n_ge otteniamo (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fact fact₁ : |u n - l| ≤ ε/2
    from hN₁ applicato a n usando hn₁
  Fact fact₂ : |v n - l'| ≤ ε/2
    from hN₂ applicato a n usando hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| by We compute
                     _ ≤ |u n - l| + |v n - l'|     by We apply abs_add
                     _ ≤  ε/2 + ε/2                 by We combine [fact₁, fact₂]
                     _ =  ε                         by We compute
QED

Example "The squeeze theorem."
  Given: (u v w : ℕ → ℝ) (l : ℝ)
  Assume: (hu : u tende a l) (hw : w tende a l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusion: v tende a l
Proof:
  Dimostriamo che ∀ ε > 0, ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Sia ε > 0
  Since u tende a l and ε > 0 otteniamo N tale che hN : ∀ n ≥ N, |u n - l| ≤ ε
  Since w tende a l and ε > 0 otteniamo N' tale che hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Dimostriamo che max N N' funziona : ∀ n ≥ max N N', |v n - l| ≤ ε
  Sia n ≥ max N N'
  Since n ≥ max N N' otteniamo (hn : n ≥ N) and (hn' : n ≥ N')
  Since ∀ n ≥ N, |u n - l| ≤ ε and n ≥ N otteniamo
   (hNl : -ε ≤ u n - l) and (hNd : u n - l ≤ ε)
  Since ∀ n ≥ N', |w n - l| ≤ ε and n ≥ N' otteniamo
    (hN'l : -ε ≤ w n - l) and (hN'd : w n - l ≤ ε)
  Dimostriamo che |v n - l| ≤ ε
  Let's first prove that -ε ≤ v n - l
  Calc -ε ≤ u n - l by assumption
      _   ≤ v n - l since u n ≤ v n
  Let's now prove that v n - l ≤ ε
  Calc v n - l ≤ w n - l  since v n ≤ w n
      _        ≤ ε        by assumption
QED

Example "A reformulation of the convergence definition."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume:
  Conclusion: (u tende a l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Proof:
  Let's first prove that (u tende a l) ⇒ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Assume hyp : u tende a l
  Sia ε > 0
  Per hyp applicato a ε/2 usando that ε/2 > 0 otteniamo N
      tale che hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Dimostriamo che N funziona
  Sia n ≥ N
  Calc |u n - l| ≤ ε/2  from hN applicato a n usando that n ≥ N
       _         < ε    since ε > 0
  Let's now prove that (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) ⇒ u tende a l
  Assume hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Sia ε > 0
  Per hyp applicato a ε usando that ε > 0 otteniamo N tale che hN : ∀ n ≥ N, |u n - l| < ε
  Dimostriamo che N funziona
  Sia n ≥ N
  Noi concludiamo per hN applicato a n usando that n ≥ N
QED


Example "Uniqueness of limits."
  Given: (u : ℕ → ℝ) (l l' : ℝ)
  Assume: (h : u tende a l) (h': u tende a l')
  Conclusion: l = l'
Proof:
  Per eq_of_forall_dist_le è sufficiente dimostrare that ∀ ε > 0, |l - l'| ≤ ε
  Sia ε > 0
  Per h applicato a ε/2 usando that ε/2 > 0 otteniamo N
      tale che hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Per h' applicato a  ε/2 usando that ε/2 > 0 otteniamo N'
      tale che hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Per hN applicato a max N N' usando le_max_left _ _
     otteniamo hN₁ : |u (max N N') - l| ≤ ε / 2
  Per hN' applicato a max N N' usando le_max_right _ _
    otteniamo hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  by We compute
  _             ≤ |l - u (max N N')| + |u (max N N') - l'| by We apply abs_add
  _             = |u (max N N') - l| + |u (max N N') - l'| by We rewrite usando abs_sub_comm
  _             ≤ ε                                        by We combine [hN₁, hN'₁]
QED

Example "An increasing sequence having a finite supremum tends to it."
  Given: (u : ℕ → ℝ) (M : ℝ)
  Assume: (h : M is a supremum of u) (h' : u is increasing)
  Conclusion: u tende a M
Proof:
  Sia ε > 0
  Per h otteniamo (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Per sup_M_ep applicato a ε usando that ε > 0 otteniamo n₀ tale che (hn₀ : u n₀ ≥ M - ε)
  Dimostriamo che n₀ funziona : ∀ n ≥ n₀, |u n - M| ≤ ε
  Sia n ≥ n₀
  Per inf_M applicato a n otteniamo (inf_M' : u n ≤ M)
  Let's first prove that -ε ≤ u n - M
  · Per h' applicato a n₀ and n usando n_ge otteniamo h'' : u n₀ ≤ u n
    We combine [h'', hn₀]
  Let's now prove that u n - M ≤ ε
  ·  We combine [inf_M', ε_pos]
QED
