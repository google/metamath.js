include "cle.mm"
include "cicc.mm"
include "df-icc.mm"
include "ixxssxr.mm"

theorem iccssxr
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A [,] B ) C_ RR*

  proof
    vx
    vy
    vz
    cA
    cB
    cle
    cle
    cicc
    vx
    vy
    vz
    df-icc
    ixxssxr
end
