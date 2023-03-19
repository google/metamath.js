include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wsbc.mm"
include "wi.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcng.mm"
include "ax-mp.mm"
include "crab.mm"
include "eleq2i.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "bitri.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "rspccv.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "con4d.mm"
include "ralrimiva.mm"

theorem bnj23
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  assume bnj23.1: |- B = { x e. A | -. ph }

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint R y
  disjoint R z
  assert |- ( A. z e. B -. z R y -> A. w e. A ( w R y -> [. w / x ]. ph ) )

  proof
    vz
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vz
    cB
    wral
    #
    vw
    cv
    #
    @1
    cR
    wbr
    #
    wph
    vx
    @5
    wsbc
    #
    wi
    vw
    cA
    @4
    @5
    cA
    wcel
    #
    wa
    #
    @7
    @6
    @7
    wn
    #
    wph
    wn
    #
    vx
    @5
    wsbc
    #
    @9
    @6
    wn
    #
    @5
    cvv
    wcel
    @12
    @10
    wb
    vw
    vex
    wph
    vx
    @5
    cvv
    sbcng
    ax-mp
    @4
    @8
    @12
    @13
    @8
    @12
    wa
    #
    @5
    cB
    wcel
    #
    @4
    @13
    @15
    @5
    @11
    vx
    cA
    crab
    #
    wcel
    @14
    cB
    @16
    @5
    bnj23.1
    eleq2i
    @11
    vx
    @5
    cA
    vx
    cA
    nfcv
    elrabsf
    bitri
    @3
    @13
    vz
    @5
    cB
    vz
    vw
    weq
    @2
    @6
    @0
    @5
    @1
    cR
    breq1
    notbid
    rspccv
    syl5bir
    expdimp
    syl5bir
    con4d
    ralrimiva
end
