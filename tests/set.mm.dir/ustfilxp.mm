include "c0.mm"
include "wne.mm"
include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfbas.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "cfil.mm"
include "wss.mm"
include "wnel.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "isust.mm"
include "syl.mm"
include "ibi.mm"
include "adantl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ne0i.mm"
include "wn.mm"
include "simp3d.mm"
include "r19.21bi.mm"
include "cop.mm"
include "vex.mm"
include "opelresi.mm"
include "ax-mp.mm"
include "biimpri.mm"
include "rgen.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "rexlimivw.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "nelrdva.mm"
include "df-nel.mm"
include "sylibr.mm"
include "inex2.mm"
include "pwid.mm"
include "a1i.mm"
include "elind.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "xpexg.mm"
include "isfbas.mm"
include "mpbir2and.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "exbii.mm"
include "an32s.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "isfil.mm"
include "sylanbrc.mm"

theorem ustfilxp
  let cU: class U
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cV: class V
  let cW: class W


  assert |- ( ( X =/= (/) /\ U e. ( UnifOn ` X ) ) -> U e. ( Fil ` ( X X. X ) ) )

  proof
    cX
    c0
    wne
    #
    cU
    cX
    cust
    cfv
    wcel
    #
    wa
    #
    cU
    cX
    cX
    cxp
    #
    cfbas
    cfv
    wcel
    #
    cU
    vw
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    @5
    cU
    wcel
    #
    wi
    #
    vw
    @3
    cpw
    #
    wral
    cU
    @3
    cfil
    cfv
    wcel
    @2
    @4
    cU
    @11
    wss
    #
    cU
    c0
    wne
    #
    c0
    cU
    wnel
    #
    cU
    vv
    cv
    #
    @5
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vw
    cU
    wral
    #
    vv
    cU
    wral
    #
    w3a
    #
    @2
    @12
    @3
    cU
    wcel
    #
    @15
    @5
    wss
    #
    @9
    wi
    #
    vw
    @11
    wral
    #
    @16
    cU
    wcel
    #
    vw
    cU
    wral
    #
    cid
    cX
    cres
    #
    @15
    wss
    #
    @15
    ccnv
    cU
    wcel
    #
    @5
    @5
    ccom
    @15
    wss
    vw
    cU
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    cU
    wral
    #
    @1
    @12
    @23
    @35
    w3a
    #
    @0
    @1
    @36
    @1
    cX
    cvv
    wcel
    #
    @1
    @36
    wb
    cU
    cX
    cust
    elfvex
    #
    vw
    vv
    cU
    cvv
    cX
    isust
    syl
    ibi
    adantl
    #
    simp1d
    @2
    @13
    @14
    @21
    @2
    @23
    @13
    @2
    @12
    @23
    @35
    @39
    simp2d
    cU
    @3
    ne0i
    syl
    @2
    c0
    cU
    wcel
    wn
    @14
    @2
    vv
    cU
    c0
    @2
    @15
    cU
    wcel
    #
    wa
    #
    @30
    @29
    c0
    wne
    #
    @15
    c0
    wne
    @41
    @30
    @31
    @32
    @41
    @26
    @28
    @33
    @2
    @34
    vv
    cU
    @2
    @12
    @23
    @35
    @39
    simp3d
    r19.21bi
    #
    simp3d
    simp1d
    @41
    @5
    @5
    cop
    #
    @29
    wcel
    #
    vw
    cX
    wrex
    #
    @42
    @0
    @46
    @1
    @40
    @0
    @45
    vw
    cX
    wral
    @46
    @45
    vw
    cX
    @45
    @5
    cX
    wcel
    #
    @5
    cvv
    wcel
    @45
    @47
    wb
    vw
    vex
    #
    @5
    cX
    cvv
    opelresi
    ax-mp
    biimpri
    rgen
    @45
    vw
    cX
    r19.2z
    mpan2
    ad2antrr
    @45
    @42
    vw
    cX
    @29
    @44
    ne0i
    rexlimivw
    syl
    @29
    @15
    ssn0
    syl2anc
    nelrdva
    c0
    cU
    df-nel
    sylibr
    @2
    @20
    vv
    cU
    @41
    @19
    vw
    cU
    @41
    @9
    wa
    #
    @16
    @18
    wcel
    @19
    @49
    cU
    @17
    @16
    @41
    @27
    vw
    cU
    @41
    @26
    @28
    @33
    @43
    simp2d
    r19.21bi
    @16
    @17
    wcel
    @49
    @16
    @5
    @15
    @48
    inex2
    pwid
    a1i
    elind
    @18
    @16
    ne0i
    syl
    ralrimiva
    ralrimiva
    3jca
    @1
    @4
    @12
    @22
    wa
    wb
    #
    @0
    @1
    @3
    cvv
    wcel
    #
    @50
    @1
    @37
    @37
    @51
    @38
    @38
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    vv
    vw
    cvv
    @3
    cU
    isfbas
    syl
    adantl
    mpbir2and
    @2
    @10
    vw
    @11
    @8
    @40
    @24
    wa
    #
    vv
    wex
    #
    @2
    @5
    @11
    wcel
    #
    wa
    #
    @9
    @8
    @15
    @7
    wcel
    #
    vv
    wex
    @53
    vv
    @7
    n0
    @56
    @52
    vv
    @56
    @40
    @15
    @6
    wcel
    #
    wa
    @52
    @15
    cU
    @6
    elin
    @57
    @24
    @40
    vv
    @5
    selpw
    anbi2i
    bitri
    exbii
    bitri
    @55
    @52
    @9
    vv
    @55
    @40
    @24
    @9
    @2
    @40
    @54
    @25
    @41
    @25
    vw
    @11
    @41
    @26
    @28
    @33
    @43
    simp1d
    r19.21bi
    an32s
    expimpd
    exlimdv
    syl5bi
    ralrimiva
    vw
    cU
    @3
    isfil
    sylanbrc
end
