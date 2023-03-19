include "cfn.mm"
include "wcel.mm"
include "cwdom.mm"
include "wbr.mm"
include "cdom.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "0domg.mm"
include "syl.mm"
include "breq1.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wb.mm"
include "brwdomn0.mm"
include "wf.mm"
include "vex.mm"
include "fof.mm"
include "dmfex.mm"
include "sylancr.mm"
include "simpl.mm"
include "simpr.mm"
include "fodomfi2.mm"
include "syl3anc.mm"
include "ex.mm"
include "adantr.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "pm2.61dane.mm"
include "domwdom.mm"
include "impbid1.mm"

theorem wdomfil
  let cX: class X
  let cY: class Y
  let cA: class A
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cV: class V


  assert |- ( X e. Fin -> ( X ~<_* Y <-> X ~<_ Y ) )

  proof
    cX
    cfn
    wcel
    #
    cX
    cY
    cwdom
    wbr
    #
    cX
    cY
    cdom
    wbr
    #
    @0
    @1
    @2
    wi
    #
    cX
    c0
    cX
    c0
    wceq
    #
    @3
    @0
    @1
    @2
    @4
    c0
    cY
    cdom
    wbr
    #
    @1
    cY
    cvv
    wcel
    #
    @5
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    cY
    cvv
    0domg
    syl
    cX
    c0
    cY
    cdom
    breq1
    syl5ibr
    adantl
    @0
    cX
    c0
    wne
    #
    wa
    #
    @1
    cY
    cX
    vx
    cv
    #
    wfo
    #
    vx
    wex
    #
    @2
    @7
    @1
    @11
    wb
    @0
    vx
    cX
    cY
    brwdomn0
    adantl
    @8
    @10
    @2
    vx
    @0
    @10
    @2
    wi
    @7
    @0
    @10
    @2
    @0
    @10
    wa
    @6
    @0
    @10
    @2
    @10
    @6
    @0
    @10
    @9
    cvv
    wcel
    cY
    cX
    @9
    wf
    @6
    vx
    vex
    cY
    cX
    @9
    fof
    cY
    cX
    cvv
    @9
    dmfex
    sylancr
    adantl
    @0
    @10
    simpl
    @0
    @10
    simpr
    cY
    cX
    @9
    cvv
    fodomfi2
    syl3anc
    ex
    adantr
    exlimdv
    sylbid
    pm2.61dane
    cX
    cY
    domwdom
    impbid1
end
