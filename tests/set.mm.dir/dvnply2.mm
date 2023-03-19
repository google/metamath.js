include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cply.mm"
include "cn0.mm"
include "cc.mm"
include "cdvn.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "wss.mm"
include "cpm.mm"
include "ssid.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "plyf.mm"
include "adantl.mm"
include "fpmg.mm"
include "syl3anc.mm"
include "dvn0.mm"
include "sylancr.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "cdv.mm"
include "dvply2g.mm"
include "ex.mm"
include "ad2antrr.mm"
include "dvnp1.mm"
include "mp3an1.mm"
include "sylan.mm"
include "sylibrd.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"
include "3impa.mm"

theorem dvnply2
  let cS: class S
  let cF: class F
  let cN: class N
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( S e. ( SubRing ` CCfld ) /\ F e. ( Poly ` S ) /\ N e. NN0 ) -> ( ( CC Dn F ) ` N ) e. ( Poly ` S ) )

  proof
    cS
    ccnfld
    csubrg
    cfv
    wcel
    #
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cc
    cF
    cdvn
    co
    #
    cfv
    #
    @1
    wcel
    #
    @3
    @0
    @2
    wa
    #
    @6
    @7
    vx
    cv
    #
    @4
    cfv
    #
    @1
    wcel
    #
    wi
    @7
    cc0
    @4
    cfv
    #
    @1
    wcel
    #
    wi
    @7
    vn
    cv
    #
    @4
    cfv
    #
    @1
    wcel
    #
    wi
    @7
    @13
    c1
    caddc
    co
    #
    @4
    cfv
    #
    @1
    wcel
    #
    wi
    @7
    @6
    wi
    vx
    vn
    cN
    @8
    cc0
    wceq
    #
    @10
    @12
    @7
    @19
    @9
    @11
    @1
    @8
    cc0
    @4
    fveq2
    eleq1d
    imbi2d
    @8
    @13
    wceq
    #
    @10
    @15
    @7
    @20
    @9
    @14
    @1
    @8
    @13
    @4
    fveq2
    eleq1d
    imbi2d
    @8
    @16
    wceq
    #
    @10
    @18
    @7
    @21
    @9
    @17
    @1
    @8
    @16
    @4
    fveq2
    eleq1d
    imbi2d
    @8
    cN
    wceq
    #
    @10
    @6
    @7
    @22
    @9
    @5
    @1
    @8
    cN
    @4
    fveq2
    eleq1d
    imbi2d
    @7
    @11
    cF
    @1
    @7
    cc
    cc
    wss
    #
    cF
    cc
    cc
    cpm
    co
    wcel
    #
    @11
    cF
    wceq
    cc
    ssid
    #
    @7
    cc
    cvv
    wcel
    #
    @26
    cc
    cc
    cF
    wf
    #
    @24
    @26
    @7
    cnex
    a1i
    #
    @28
    @2
    @27
    @0
    cS
    cF
    plyf
    adantl
    cc
    cc
    cF
    cvv
    cvv
    fpmg
    syl3anc
    #
    cc
    cF
    dvn0
    sylancr
    @0
    @2
    simpr
    eqeltrd
    @13
    cn0
    wcel
    #
    @7
    @15
    @18
    @7
    @30
    @15
    @18
    wi
    @7
    @30
    wa
    #
    @15
    cc
    @14
    cdv
    co
    #
    @1
    wcel
    #
    @18
    @0
    @15
    @33
    wi
    @2
    @30
    @0
    @15
    @33
    cS
    @14
    dvply2g
    ex
    ad2antrr
    @31
    @17
    @32
    @1
    @7
    @24
    @30
    @17
    @32
    wceq
    #
    @29
    @23
    @24
    @30
    @34
    @25
    cc
    cF
    @13
    dvnp1
    mp3an1
    sylan
    eleq1d
    sylibrd
    expcom
    a2d
    nn0ind
    impcom
    3impa
end
