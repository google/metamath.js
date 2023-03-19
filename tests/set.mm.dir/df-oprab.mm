
axiom df-oprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- { <. <. x , y >. , z >. | ph } = { w | E. x E. y E. z ( w = <. <. x , y >. , z >. /\ ph ) }
end
