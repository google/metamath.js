include "cle.mm"
include "cicc.mm"
include "df-icc.mm"
include "ixxf.mm"

theorem iccf
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- [,] : ( RR* X. RR* ) --> ~P RR*

  proof
    vx
    vy
    vz
    cle
    cle
    cicc
    vx
    vy
    vz
    df-icc
    ixxf
end
