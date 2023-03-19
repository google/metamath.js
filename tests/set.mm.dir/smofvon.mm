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
include "simp1bi.mm"
include "ffvelrnda.mm"

theorem smofvon
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F


  assert |- ( ( Smo B /\ A e. dom B ) -> ( B ` A ) e. On )

  proof
    cB
    wsmo
    #
    cB
    cdm
    #
    con0
    cA
    cB
    @0
    @1
    con0
    cB
    wf
    @1
    word
    vx
    cv
    #
    vy
    cv
    #
    wcel
    @2
    cB
    cfv
    @3
    cB
    cfv
    wcel
    wi
    vy
    @1
    wral
    vx
    @1
    wral
    vx
    vy
    cB
    df-smo
    simp1bi
    ffvelrnda
end
