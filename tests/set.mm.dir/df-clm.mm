
axiom df-clm
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- CMod = { w e. LMod | [. ( Scalar ` w ) / f ]. [. ( Base ` f ) / k ]. ( f = ( CCfld |`s k ) /\ k e. ( SubRing ` CCfld ) ) }
end
