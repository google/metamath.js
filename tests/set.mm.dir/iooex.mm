include "clt.mm"
include "cioo.mm"
include "df-ioo.mm"
include "ixxex.mm"

theorem iooex
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- (,) e. _V

  proof
    vx
    vy
    vz
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    ixxex
end
