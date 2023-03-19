include "ccusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "cv.mm"
include "wi.mm"
include "nfielex.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "cdif.mm"
include "cmpt.mm"
include "weq.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "cusgrfilem3.mm"
include "notbid.mm"
include "biimpac.mm"
include "cedg.mm"
include "cfv.mm"
include "wss.mm"
include "cusgrfilem1.mm"
include "eleq1i.mm"
include "ssfi.mm"
include "expcom.mm"
include "syl5bi.mm"
include "con3d.mm"
include "syl.mm"
include "com23.mm"
include "adantl.mm"
include "mpd.mm"
include "exlimddv.mm"
include "com12.mm"
include "con4d.mm"
include "imp.mm"

theorem cusgrfi
  let cE: class E
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vp: setvar p
  let ve: setvar e
  let vv: setvar v
  assume cusgrfi.v: |- V = ( Vtx ` G )
  assume cusgrfi.e: |- E = ( Edg ` G )


  assert |- ( ( G e. ComplUSGraph /\ E e. Fin ) -> V e. Fin )

  proof
    cG
    ccusgr
    wcel
    #
    cE
    cfn
    wcel
    #
    cV
    cfn
    wcel
    #
    @0
    @2
    @1
    @2
    wn
    #
    @0
    @1
    wn
    #
    @3
    vn
    cv
    #
    cV
    wcel
    #
    @0
    @4
    wi
    #
    vn
    vn
    cV
    nfielex
    @3
    @6
    wa
    vv
    cv
    #
    @5
    wne
    #
    ve
    cv
    #
    @8
    @5
    cpr
    #
    wceq
    #
    wa
    #
    vv
    cV
    wrex
    #
    ve
    cV
    cpw
    #
    crab
    #
    cfn
    wcel
    #
    wn
    #
    @7
    @6
    @3
    @18
    @6
    @2
    @17
    vp
    @16
    vp
    cV
    @5
    csn
    cdif
    vp
    cv
    #
    @5
    cpr
    cmpt
    #
    cG
    @5
    cV
    vv
    cusgrfi.v
    @14
    @9
    @19
    @11
    wceq
    #
    wa
    #
    vv
    cV
    wrex
    ve
    vp
    @15
    ve
    vp
    weq
    #
    @13
    @22
    vv
    cV
    @23
    @12
    @21
    @9
    @10
    @19
    @11
    eqeq1
    anbi2d
    rexbidv
    cbvrabv
    #
    @20
    eqid
    cusgrfilem3
    notbid
    biimpac
    @6
    @18
    @7
    wi
    @3
    @6
    @0
    @18
    @4
    @0
    @6
    @18
    @4
    wi
    #
    @0
    @6
    wa
    @16
    cG
    cedg
    cfv
    #
    wss
    #
    @25
    vp
    @16
    cG
    @5
    cV
    vv
    cusgrfi.v
    @24
    cusgrfilem1
    @27
    @1
    @17
    @1
    @26
    cfn
    wcel
    #
    @27
    @17
    cE
    @26
    cfn
    cusgrfi.e
    eleq1i
    @28
    @27
    @17
    @26
    @16
    ssfi
    expcom
    syl5bi
    con3d
    syl
    expcom
    com23
    adantl
    mpd
    exlimddv
    com12
    con4d
    imp
end
