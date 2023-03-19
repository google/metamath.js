include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cdif.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "ssid.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "onelon.mm"
include "ancoms.mm"
include "cdm.mm"
include "wfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "fnfun.mm"
include "funfvima.mm"
include "mpan.mm"
include "impcom.mm"
include "eleq1a.mm"
include "eldifn.mm"
include "nsyli.mm"
include "syl.mm"
include "sylan2br.mm"
include "syldan.mm"
include "expimpd.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ralimiaa.mm"
include "tz7.48lem.mm"
include "sylancr.mm"
include "wrel.mm"
include "fnrel.mm"
include "eqimssi.mm"
include "relssres.mm"
include "mp2an.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "sylib.mm"

theorem tz7.48-2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tz7.48.1: |- F Fn On

  disjoint F x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint F y
  disjoint F z
  disjoint F w
  assert |- ( A. x e. On ( F ` x ) e. ( A \ ( F " x ) ) -> Fun `' F )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    cA
    cF
    @0
    cima
    #
    cdif
    wcel
    #
    vx
    con0
    wral
    #
    cF
    con0
    cres
    #
    ccnv
    #
    wfun
    #
    cF
    ccnv
    #
    wfun
    @4
    con0
    con0
    wss
    @1
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wn
    #
    vy
    @0
    wral
    #
    vx
    con0
    wral
    @7
    con0
    ssid
    @3
    @13
    vx
    con0
    @0
    con0
    wcel
    #
    @3
    wa
    #
    @12
    vy
    @0
    vy
    vx
    wel
    #
    @15
    @12
    @16
    @14
    @3
    @12
    @16
    @14
    @9
    con0
    wcel
    #
    @3
    @12
    wi
    #
    @14
    @16
    @17
    @0
    @9
    onelon
    ancoms
    @17
    @16
    @9
    cF
    cdm
    #
    wcel
    #
    @18
    @19
    con0
    @9
    cF
    con0
    wfn
    #
    @19
    con0
    wceq
    tz7.48.1
    con0
    cF
    fndm
    ax-mp
    #
    eleq2i
    @16
    @20
    wa
    @10
    @2
    wcel
    #
    @18
    @20
    @16
    @23
    cF
    wfun
    #
    @20
    @16
    @23
    wi
    @21
    @24
    tz7.48.1
    con0
    cF
    fnfun
    ax-mp
    @0
    @9
    cF
    funfvima
    mpan
    impcom
    @23
    @11
    @1
    @2
    wcel
    @3
    @10
    @2
    @1
    eleq1a
    @1
    cA
    @2
    eldifn
    nsyli
    syl
    sylan2br
    syldan
    expimpd
    com12
    ralrimiv
    ralimiaa
    vx
    vy
    con0
    cF
    tz7.48.1
    tz7.48lem
    sylancr
    @6
    @8
    @5
    cF
    cF
    wrel
    #
    @19
    con0
    wss
    @5
    cF
    wceq
    @21
    @25
    tz7.48.1
    con0
    cF
    fnrel
    ax-mp
    @19
    con0
    @22
    eqimssi
    cF
    con0
    relssres
    mp2an
    cnveqi
    funeqi
    sylib
end
