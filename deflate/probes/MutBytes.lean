import VIRDeflate
/- MUTANT of VIRDeflate/Bytes.lean (red backwards): the input read as twice each byte, so the byte bound is no longer what the
   type gives. `ofBytes_lt`'s proof must FAIL. -/
namespace VIRDeflate.Step
def ofBytesMut (bs : ByteArray) : Array Nat := bs.data.map (fun u => u.toNat * 2)
theorem ofBytesMut_lt (bs : ByteArray) : ∀ x ∈ ofBytesMut bs, x < 256 := by
  intro x hx
  simp only [ofBytesMut, Array.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  exact UInt8.toNat_lt u
end VIRDeflate.Step
