include "ccusp.mm"
include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "cuss.mm"
include "ccfilu.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "ctopn.mm"
include "wi.mm"
include "cbs.mm"
include "wceq.mm"
include "eleq1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "id.mm"
include "oveq12d.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "wral.mm"
include "cusp.mm"
include "iscusp.mm"
include "simprbi.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "rspcdva.mm"
include "3impia.mm"
include "3com23.mm"

theorem cuspcvg
  let cB: class B
  let cC: class C
  let cJ: class J
  let cW: class W
  let vc: setvar c
  let vw: setvar w
  assume cuspcvg.1: |- B = ( Base ` W )
  assume cuspcvg.2: |- J = ( TopOpen ` W )


  assert |- ( ( W e. CUnifSp /\ C e. ( CauFilU ` ( UnifSt ` W ) ) /\ C e. ( Fil ` B ) ) -> ( J fLim C ) =/= (/) )

  proof
    cW
    ccusp
    wcel
    #
    cC
    cB
    cfil
    cfv
    #
    wcel
    #
    cC
    cW
    cuss
    cfv
    ccfilu
    cfv
    #
    wcel
    #
    cJ
    cC
    cflim
    co
    #
    c0
    wne
    #
    @0
    @2
    @4
    @6
    @0
    @2
    wa
    #
    vc
    cv
    #
    @3
    wcel
    #
    cW
    ctopn
    cfv
    #
    @8
    cflim
    co
    #
    c0
    wne
    #
    wi
    #
    @4
    @6
    wi
    vc
    cW
    cbs
    cfv
    #
    cfil
    cfv
    #
    cC
    @8
    cC
    wceq
    #
    @9
    @4
    @12
    @6
    @8
    cC
    @3
    eleq1
    @16
    @11
    @5
    c0
    @16
    @10
    cJ
    @8
    cC
    cflim
    @10
    cJ
    wceq
    @16
    cJ
    @10
    cuspcvg.2
    eqcomi
    a1i
    @16
    id
    oveq12d
    neeq1d
    imbi12d
    @0
    @13
    vc
    @15
    wral
    #
    @2
    @0
    cW
    cusp
    wcel
    @17
    cW
    vc
    iscusp
    simprbi
    adantr
    @7
    cC
    @1
    @15
    @0
    @2
    simpr
    cB
    @14
    cfil
    cuspcvg.1
    fveq2i
    syl6eleq
    rspcdva
    3impia
    3com23
end
