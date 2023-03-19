include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "nfoprab2.mm"
include "nfcxfr.mm"

theorem nfmpt22
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z


  assert |- F/_ y ( x e. A , y e. B |-> C )

  proof
    vy
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    vz
    cv
    cC
    wceq
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    @0
    vx
    vy
    vz
    nfoprab2
    nfcxfr
end
