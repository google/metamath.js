include "df-clab.mm"

theorem eliminable1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( y e. { x | ph } <-> [ y / x ] ph )

  proof
    wph
    vy
    vx
    df-clab
end
