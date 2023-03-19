include "c0.mm"
include "wne.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wf.mm"
include "wceq.mm"
include "elmapi.mm"
include "cdm.mm"
include "fdm.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "ss0.mm"
include "syl.mm"
include "dm0rn0.mm"
include "sylibr.mm"
include "eqtr3d.mm"
include "necon3ai.mm"
include "eq0rdv.mm"

theorem map0b
  let cA: class A
  let vf: setvar f
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( A =/= (/) -> ( (/) ^m A ) = (/) )

  proof
    cA
    c0
    wne
    vf
    c0
    cA
    cmap
    co
    #
    vf
    cv
    #
    @0
    wcel
    #
    cA
    c0
    @2
    cA
    c0
    @1
    wf
    #
    cA
    c0
    wceq
    @1
    c0
    cA
    elmapi
    @3
    @1
    cdm
    #
    cA
    c0
    cA
    c0
    @1
    fdm
    @3
    @1
    crn
    #
    c0
    wceq
    #
    @4
    c0
    wceq
    @3
    @5
    c0
    wss
    @6
    cA
    c0
    @1
    frn
    @5
    ss0
    syl
    @1
    dm0rn0
    sylibr
    eqtr3d
    syl
    necon3ai
    eq0rdv
end
