
axiom df-lnr
  let va: setvar a
  assert |- LNoeR = { a e. Ring | ( ringLMod ` a ) e. LNoeM }
end
