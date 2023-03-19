include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "chash.mm"
include "cres.mm"
include "cmeas.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cvv.mm"
include "wss.mm"
include "hashf2.mm"
include "ssv.mm"
include "fssres.mm"
include "mp2an.mm"
include "a1i.mm"
include "0elsiga.mm"
include "fvres.mm"
include "syl.mm"
include "hash0.mm"
include "syl6eq.mm"
include "vex.mm"
include "hasheuni.mm"
include "mpan.mm"
include "ad2antll.mm"
include "cdif.mm"
include "w3a.mm"
include "isrnsigau.mm"
include "simprd.mm"
include "simp3d.mm"
include "imim2i.mm"
include "ralimi.mm"
include "r19.21bi.mm"
include "imp.mm"
include "adantrr.mm"
include "elpwi.mm"
include "sseld.mm"
include "syl6.mm"
include "esumeq2dv.mm"
include "ad2antlr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "ismeas.mm"
include "mpbir3and.mm"

theorem cntmeas
  let cS: class S
  let vx: setvar x
  let vy: setvar y


  assert |- ( S e. U. ran sigAlgebra -> ( # |` S ) e. ( measures ` S ) )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    chash
    cS
    cres
    #
    cS
    cmeas
    cfv
    wcel
    cS
    cc0
    cpnf
    cicc
    co
    #
    @1
    wf
    #
    c0
    @1
    cfv
    #
    cc0
    wceq
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @5
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @5
    cuni
    #
    @1
    cfv
    #
    @5
    @7
    @1
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    cS
    cpw
    #
    wral
    @3
    @0
    cvv
    @2
    chash
    wf
    cS
    cvv
    wss
    @3
    hashf2
    cS
    ssv
    cvv
    @2
    cS
    chash
    fssres
    mp2an
    a1i
    @0
    @4
    c0
    chash
    cfv
    #
    cc0
    @0
    c0
    cS
    wcel
    @4
    @17
    wceq
    cS
    0elsiga
    c0
    cS
    chash
    fvres
    syl
    hash0
    syl6eq
    @0
    @15
    vx
    @16
    @0
    @5
    @16
    wcel
    #
    wa
    #
    @9
    @14
    @19
    @9
    wa
    @10
    chash
    cfv
    #
    @5
    @7
    chash
    cfv
    #
    vy
    cesum
    #
    @11
    @13
    @8
    @20
    @22
    wceq
    #
    @19
    @6
    @5
    cvv
    wcel
    @8
    @23
    vx
    vex
    vy
    @5
    cvv
    hasheuni
    mpan
    ad2antll
    @19
    @6
    @11
    @20
    wceq
    #
    @8
    @19
    @6
    @24
    @0
    @6
    @24
    wi
    #
    vx
    @16
    @0
    @6
    @10
    cS
    wcel
    #
    wi
    #
    vx
    @16
    wral
    #
    @25
    vx
    @16
    wral
    @0
    cS
    cuni
    #
    cS
    wcel
    #
    @29
    @5
    cdif
    cS
    wcel
    vx
    cS
    wral
    #
    @28
    @0
    cS
    @29
    cpw
    wss
    @30
    @31
    @28
    w3a
    vx
    cS
    isrnsigau
    simprd
    simp3d
    @27
    @25
    vx
    @16
    @26
    @24
    @6
    @10
    cS
    chash
    fvres
    imim2i
    ralimi
    syl
    r19.21bi
    imp
    adantrr
    @18
    @13
    @22
    wceq
    @0
    @9
    @18
    @5
    @12
    @21
    vy
    @18
    @7
    @5
    wcel
    #
    @12
    @21
    wceq
    #
    @18
    @32
    @7
    cS
    wcel
    @33
    @18
    @5
    cS
    @7
    @5
    cS
    elpwi
    sseld
    @7
    cS
    chash
    fvres
    syl6
    imp
    esumeq2dv
    ad2antlr
    3eqtr4d
    ex
    ralrimiva
    vx
    vy
    cS
    @1
    ismeas
    mpbir3and
end
