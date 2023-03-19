
axiom df-tdrg
  let vr: setvar r
  assert |- TopDRing = { r e. ( TopRing i^i DivRing ) | ( ( mulGrp ` r ) |`s ( Unit ` r ) ) e. TopGrp }
end
