import CodedSorting.Interchange.Binary.Normalized
import CodedSorting.Interchange.Bounds.ExchangeSpace
import CodedSorting.Interchange.Bounds.ExchangeCapacity

/-! Selected axiom audit for the actual arbitrary-width and binary Construction
exchange. The program keeps its original finite machine and executes real
borrowing, padding, chunk exchange, erasure and restoration instructions.
The normalized interface still exposes source separation and finite disk/
program-counter obligations; the capacity lemmas establish numerical bounds.
These endpoints audit the arbitrary-width exchange component used by sorting. -/

namespace CodedSorting.Construction.ArbitraryExchangeAudit

#print axioms ArbitraryCalls.Call.width_zero
#print axioms ArbitraryCalls.calls_width
#print axioms ArbitraryCalls.baseCalls_width
#print axioms ArbitraryCalls.paddedRows_zero
#print axioms ArbitraryCalls.generated_padding_le_twice
#print axioms ArbitraryCalls.calls_fit

#print axioms ChunkExchange.oneProgram
#print axioms ChunkExchange.oneProgram_charge
#print axioms ChunkExchange.program
#print axioms ChunkExchange.program_charge
#print axioms PaddedChunks.program
#print axioms PaddedChunks.program_charge_le
#print axioms BorrowedChunks.program
#print axioms BorrowedChunks.program_charge_le

#print axioms ArbitraryMachine.complete_improved
#print axioms BinaryCost.bound_improved
#print axioms BinaryMachine.program
#print axioms BinaryMachine.complete_improved
#print axioms BinaryNormalized.normalizedProgram
#print axioms BinaryNormalized.normalized_bound
#print axioms BinaryNormalized.normalized_base_scale

#print axioms ExchangeSpace.binary
#print axioms ExchangeSpace.root_allocation_fits
#print axioms ExchangeCapacity.bound_fits
#print axioms ExchangeCapacity.input_width_le

end CodedSorting.Construction.ArbitraryExchangeAudit
