import VIRL2.Store
open VIRL1 VIRL2
example {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .load vs σ = some (v, σ')) : False := by
  unfold opStep at h
  split at h
  all_goals trace_state
  all_goals sorry
example {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .store vs σ = some (v, σ')) : False := by
  unfold opStep at h
  split at h
  all_goals trace_state
  all_goals sorry
