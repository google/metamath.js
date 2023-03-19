include "wcel.mm"
include "cmre.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "mresspw.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "a1i.mm"
include "ssid.mm"
include "pwidg.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "cuni.mm"
include "intssuni2.mm"
include "3adant1.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "wb.mm"
include "elpw2g.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "ismred.mm"
include "wel.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "intss1.mm"
include "adantl.mm"
include "simpr.mm"
include "sselda.mm"
include "syl.mm"
include "sstrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"
include "wral.mm"
include "simp2.mm"
include "mre1cl.mm"
include "ralrimiva.mm"
include "elintg.mm"
include "simp12.mm"
include "simpl2.mm"
include "simpl3.mm"
include "mreintcl.mm"
include "syl3anc.mm"
include "cvv.mm"
include "intex.mm"
include "sylbi.mm"
include "3ad2ant3.mm"

theorem mremre
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( X e. V -> ( Moore ` X ) e. ( Moore ` ~P X ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cmre
    cfv
    #
    cX
    cpw
    #
    va
    @1
    @2
    cpw
    #
    wss
    @0
    va
    @1
    @3
    va
    cv
    #
    @1
    wcel
    @4
    @2
    wss
    #
    @4
    @3
    wcel
    @4
    cX
    mresspw
    va
    @2
    selpw
    sylibr
    ssriv
    a1i
    @0
    @2
    cX
    va
    @2
    @2
    wss
    @0
    @2
    ssid
    a1i
    cX
    cV
    pwidg
    @0
    @5
    @4
    c0
    wne
    #
    w3a
    #
    @4
    cint
    #
    @2
    wcel
    #
    @8
    cX
    wss
    #
    @7
    @8
    @2
    cuni
    #
    cX
    @5
    @6
    @8
    @11
    wss
    @0
    @4
    @2
    intssuni2
    3adant1
    cX
    unipw
    syl6sseq
    @0
    @5
    @9
    @10
    wb
    @6
    @8
    cX
    cV
    elpw2g
    3ad2ant1
    mpbird
    ismred
    @0
    @4
    @1
    wss
    #
    @6
    w3a
    #
    @8
    cX
    vb
    @0
    @12
    @6
    @8
    @2
    wss
    #
    @6
    vb
    va
    wel
    #
    vb
    wex
    @0
    @12
    wa
    #
    @14
    vb
    @4
    n0
    @16
    @15
    @14
    vb
    @16
    @15
    @14
    @16
    @15
    wa
    #
    @8
    vb
    cv
    #
    @2
    @15
    @8
    @18
    wss
    @16
    @18
    @4
    intss1
    adantl
    @17
    @18
    @1
    wcel
    #
    @18
    @2
    wss
    @16
    @4
    @1
    @18
    @0
    @12
    simpr
    sselda
    @18
    cX
    mresspw
    syl
    sstrd
    ex
    exlimdv
    syl5bi
    3impia
    @13
    cX
    @8
    wcel
    #
    cX
    @18
    wcel
    #
    vb
    @4
    wral
    #
    @13
    @21
    vb
    @4
    @13
    @15
    wa
    @19
    @21
    @13
    @4
    @1
    @18
    @0
    @12
    @6
    simp2
    sselda
    @18
    cX
    mre1cl
    syl
    ralrimiva
    @0
    @12
    @20
    @22
    wb
    @6
    vb
    cX
    @4
    cV
    elintg
    3ad2ant1
    mpbird
    @13
    @18
    @8
    wss
    #
    @18
    c0
    wne
    #
    w3a
    #
    @18
    cint
    #
    @8
    wcel
    #
    @26
    vc
    cv
    #
    wcel
    #
    vc
    @4
    wral
    #
    @25
    @29
    vc
    @4
    @25
    vc
    va
    wel
    #
    wa
    #
    @28
    @1
    wcel
    @18
    @28
    wss
    @24
    @29
    @25
    @4
    @1
    @28
    @0
    @12
    @6
    @23
    @24
    simp12
    sselda
    @32
    @18
    @8
    @28
    @13
    @23
    @24
    @31
    simpl2
    @31
    @8
    @28
    wss
    @25
    @28
    @4
    intss1
    adantl
    sstrd
    @13
    @23
    @24
    @31
    simpl3
    @28
    @18
    cX
    mreintcl
    syl3anc
    ralrimiva
    @24
    @13
    @27
    @30
    wb
    #
    @23
    @24
    @26
    cvv
    wcel
    @33
    @18
    intex
    vc
    @26
    @4
    cvv
    elintg
    sylbi
    3ad2ant3
    mpbird
    ismred
    ismred
end
