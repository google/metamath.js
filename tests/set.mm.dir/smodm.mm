include "wsmo.mm"
include "cdm.mm"
include "con0.mm"
include "wf.mm"
include "word.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "df-smo.mm"
include "simp2bi.mm"

theorem smodm
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( Smo A -> Ord dom A )

  proof
    cA
    wsmo
    cA
    cdm
    #
    con0
    cA
    wf
    @0
    word
    vx
    cv
    #
    vy
    cv
    #
    wcel
    @1
    cA
    cfv
    @2
    cA
    cfv
    wcel
    wi
    vy
    @0
    wral
    vx
    @0
    wral
    vx
    vy
    cA
    df-smo
    simp2bi
end
