include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wcel.mm"
include "ucnima.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cfv.mm"
include "cop.mm"
include "mpt2fun.mm"
include "cxp.mm"
include "cust.mm"
include "ustssxp.mm"
include "sylan.mm"
include "opex.mm"
include "dmmpt2.mm"
include "syl6sseqr.mm"
include "funimass3.mm"
include "sylancr.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "wi.mm"
include "adantr.mm"
include "simpr.mm"
include "cnvimass.mm"
include "sseqtri.mm"
include "a1i.mm"
include "ustssel.mm"
include "syl3anc.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem ucnprima
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vr: setvar r
  let vw: setvar w
  assume ucnprima.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume ucnprima.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume ucnprima.3: |- ( ph -> F e. ( U uCn V ) )
  assume ucnprima.4: |- ( ph -> W e. V )
  assume ucnprima.5: |- G = ( x e. X , y e. X |-> <. ( F ` x ) , ( F ` y ) >. )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint G x
  disjoint G y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint W x
  disjoint W y
  disjoint Y x
  disjoint ph x
  disjoint ph y
  disjoint p x
  disjoint p y
  disjoint F p
  disjoint X p
  disjoint p r
  disjoint p w
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint G p
  disjoint U p
  disjoint U r
  disjoint U w
  disjoint V r
  disjoint V w
  disjoint W p
  disjoint W r
  disjoint W w
  disjoint X r
  disjoint X w
  disjoint Y r
  disjoint Y w
  disjoint p ph
  disjoint ph r
  disjoint G r
  assert |- ( ph -> ( `' G " W ) e. U )

  proof
    wph
    vr
    cv
    #
    cG
    ccnv
    cW
    cima
    #
    wss
    #
    vr
    cU
    wrex
    #
    @1
    cU
    wcel
    #
    wph
    cG
    @0
    cima
    cW
    wss
    #
    vr
    cU
    wrex
    @3
    wph
    vx
    vy
    cU
    cF
    cG
    cV
    cW
    cX
    cY
    vr
    ucnprima.1
    ucnprima.2
    ucnprima.3
    ucnprima.4
    ucnprima.5
    ucnima
    wph
    @5
    @2
    vr
    cU
    wph
    @0
    cU
    wcel
    #
    wa
    #
    cG
    wfun
    @0
    cG
    cdm
    #
    wss
    @5
    @2
    wb
    vx
    vy
    cX
    cX
    vx
    cv
    cF
    cfv
    #
    vy
    cv
    cF
    cfv
    #
    cop
    #
    cG
    ucnprima.5
    mpt2fun
    @7
    @0
    cX
    cX
    cxp
    #
    @8
    wph
    cU
    cX
    cust
    cfv
    wcel
    #
    @6
    @0
    @12
    wss
    ucnprima.1
    cU
    @0
    cX
    ustssxp
    sylan
    vx
    vy
    cX
    cX
    @11
    cG
    ucnprima.5
    @9
    @10
    opex
    dmmpt2
    #
    syl6sseqr
    @0
    cW
    cG
    funimass3
    sylancr
    rexbidva
    mpbid
    wph
    @2
    @4
    vr
    cU
    @7
    @13
    @6
    @1
    @12
    wss
    #
    @2
    @4
    wi
    wph
    @13
    @6
    ucnprima.1
    adantr
    wph
    @6
    simpr
    @15
    @7
    @1
    @8
    @12
    cG
    cW
    cnvimass
    @14
    sseqtri
    a1i
    cU
    @0
    @1
    cX
    ustssel
    syl3anc
    rexlimdva
    mpd
end
