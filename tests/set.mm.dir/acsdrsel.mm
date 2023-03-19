include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "wa.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "cmre.mm"
include "isacs3lem.mm"
include "simprd.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "unieq.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "3impia.mm"

theorem acsdrsel
  let cC: class C
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cS: class S


  assert |- ( ( C e. ( ACS ` X ) /\ Y C_ C /\ ( toInc ` Y ) e. Dirset ) -> U. Y e. C )

  proof
    cC
    cX
    cacs
    cfv
    #
    wcel
    #
    cY
    cC
    wss
    #
    cY
    cipo
    cfv
    #
    cdrs
    wcel
    #
    cY
    cuni
    #
    cC
    wcel
    #
    @1
    @2
    wa
    cY
    cC
    cpw
    #
    wcel
    #
    vs
    cv
    #
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @9
    cuni
    #
    cC
    wcel
    #
    wi
    #
    vs
    @7
    wral
    #
    @4
    @6
    wi
    #
    @1
    @8
    @2
    cY
    cC
    @0
    elpw2g
    biimpar
    @1
    @15
    @2
    @1
    cC
    cX
    cmre
    cfv
    wcel
    @15
    cC
    cX
    vs
    isacs3lem
    simprd
    adantr
    @14
    @16
    vs
    cY
    @7
    @9
    cY
    wceq
    #
    @11
    @4
    @13
    @6
    @17
    @10
    @3
    cdrs
    @9
    cY
    cipo
    fveq2
    eleq1d
    @17
    @12
    @5
    cC
    @9
    cY
    unieq
    eleq1d
    imbi12d
    rspcva
    syl2anc
    3impia
end
