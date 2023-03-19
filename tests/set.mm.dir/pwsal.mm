include "wcel.mm"
include "cpw.mm"
include "csalg.mm"
include "c0.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "0elpw.mm"
include "a1i.mm"
include "wceq.mm"
include "unipw.mm"
include "difeq1i.mm"
include "wss.mm"
include "difssd.mm"
include "cvv.mm"
include "wb.mm"
include "difexg.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "wa.mm"
include "elpwi.mm"
include "uniss.mm"
include "syl6sseq.mm"
include "vuniex.mm"
include "adantl.mm"
include "a1d.mm"
include "3jca.mm"
include "pwexg.mm"
include "issal.mm"

theorem pwsal
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- ( X e. V -> ~P X e. SAlg )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    csalg
    wcel
    #
    c0
    @1
    wcel
    #
    @1
    cuni
    #
    vy
    cv
    #
    cdif
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    #
    @5
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    #
    w3a
    #
    @0
    @3
    @8
    @14
    @3
    @0
    cX
    0elpw
    a1i
    @0
    @7
    vy
    @1
    @0
    @7
    @5
    @1
    wcel
    @0
    @6
    cX
    @5
    cdif
    #
    @1
    @6
    @16
    wceq
    @0
    @4
    cX
    @5
    cX
    unipw
    #
    difeq1i
    a1i
    @0
    @16
    @1
    wcel
    #
    @16
    cX
    wss
    #
    @0
    cX
    @5
    difssd
    @0
    @16
    cvv
    wcel
    @18
    @19
    wb
    cX
    @5
    cV
    difexg
    @16
    cX
    cvv
    elpwg
    syl
    mpbird
    eqeltrd
    adantr
    ralrimiva
    @0
    @12
    vy
    @13
    @0
    @5
    @13
    wcel
    #
    wa
    @11
    @9
    @20
    @11
    @0
    @20
    @11
    @10
    cX
    wss
    #
    @20
    @10
    @4
    cX
    @20
    @5
    @1
    wss
    @10
    @4
    wss
    @5
    @1
    elpwi
    @5
    @1
    uniss
    syl
    @17
    syl6sseq
    @20
    @10
    cvv
    wcel
    #
    @11
    @21
    wb
    @22
    @20
    vy
    vuniex
    a1i
    @10
    cX
    cvv
    elpwg
    syl
    mpbird
    adantl
    a1d
    ralrimiva
    3jca
    @0
    @1
    cvv
    wcel
    @2
    @15
    wb
    cX
    cV
    pwexg
    vy
    @1
    cvv
    issal
    syl
    mpbird
end
