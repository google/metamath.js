
axiom df-iota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assert |- ( iota x ph ) = U. { y | { x | ph } = { y } }
end
