include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "cpw.mm"
include "ccn.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "adantl.mm"
include "syl5sseq.mm"
include "wb.mm"
include "elpw2g.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "ralrimivw.mm"
include "ex.mm"
include "pm4.71d.mm"
include "toponmax.mm"
include "id.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "distopon.mm"
include "iscn.mm"
include "sylan.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem cndis
  let cA: class A
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cY: class Y


  assert |- ( ( A e. V /\ J e. ( TopOn ` X ) ) -> ( ~P A Cn J ) = ( X ^m A ) )

  proof
    cA
    cV
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    wa
    #
    vf
    cA
    cpw
    #
    cJ
    ccn
    co
    #
    cX
    cA
    cmap
    co
    #
    @2
    cA
    cX
    vf
    cv
    #
    wf
    #
    @7
    @6
    ccnv
    vx
    cv
    #
    cima
    #
    @3
    wcel
    #
    vx
    cJ
    wral
    #
    wa
    #
    @6
    @5
    wcel
    #
    @6
    @4
    wcel
    #
    @2
    @7
    @11
    @2
    @7
    @11
    @2
    @7
    wa
    #
    @10
    vx
    cJ
    @15
    @10
    @9
    cA
    wss
    #
    @15
    @6
    cdm
    #
    @9
    cA
    @6
    @8
    cnvimass
    @7
    @17
    cA
    wceq
    @2
    cA
    cX
    @6
    fdm
    adantl
    syl5sseq
    @0
    @10
    @16
    wb
    @1
    @7
    @9
    cA
    cV
    elpw2g
    ad2antrr
    mpbird
    ralrimivw
    ex
    pm4.71d
    @1
    cX
    cJ
    wcel
    @0
    @13
    @7
    wb
    @0
    cX
    cJ
    toponmax
    @0
    id
    cX
    cA
    @6
    cJ
    cV
    elmapg
    syl2anr
    @0
    @3
    cA
    ctopon
    cfv
    wcel
    @1
    @14
    @12
    wb
    cA
    cV
    distopon
    vx
    @6
    @3
    cJ
    cA
    cX
    iscn
    sylan
    3bitr4rd
    eqrdv
end
