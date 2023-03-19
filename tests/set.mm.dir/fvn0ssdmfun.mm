include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "wss.mm"
include "fvfundmfvn0.mm"
include "ralimi.mm"
include "r19.26.mm"
include "eleq1.mm"
include "rspccv.mm"
include "ssrdv.mm"
include "ciun.mm"
include "wrel.mm"
include "cop.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "funrel.mm"
include "reliun.mm"
include "sylibr.mm"
include "sneq.mm"
include "reseq2d.mm"
include "funeqd.mm"
include "rspcva.mm"
include "dffun5.mm"
include "vex.mm"
include "elsnres.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "equcom.mm"
include "opeq12.mm"
include "ex.mm"
include "syl5bi.mm"
include "adantr.mm"
include "impcom.mm"
include "opeq2.mm"
include "equcoms.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "adantl.mm"
include "jca.mm"
include "spimev.mm"
include "imim1d.mm"
include "alimdv.mm"
include "eximdv.mm"
include "spimvw.mm"
include "sylbi.mm"
include "syl.mm"
include "expcom.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "19.21v.mm"
include "19.37v.mm"
include "3bitri.mm"
include "alrimiv.mm"
include "resiun2.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "iunid.mm"
include "reseq2i.mm"
include "opelres.mm"
include "sylanbrc.mm"
include "funeqi.mm"
include "anim12i.mm"

theorem fvn0ssdmfun
  let cD: class D
  let cF: class F
  let va: setvar a
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint D a
  disjoint F a
  disjoint D p
  disjoint a p
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F p
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( A. a e. D ( F ` a ) =/= (/) -> ( D C_ dom F /\ Fun ( F |` D ) ) )

  proof
    va
    cv
    #
    cF
    cfv
    c0
    wne
    #
    va
    cD
    wral
    @0
    cF
    cdm
    #
    wcel
    #
    cF
    @0
    csn
    #
    cres
    #
    wfun
    #
    wa
    #
    va
    cD
    wral
    #
    cD
    @2
    wss
    #
    cF
    cD
    cres
    #
    wfun
    #
    wa
    #
    @1
    @7
    va
    cD
    @0
    cF
    fvfundmfvn0
    ralimi
    @8
    @3
    va
    cD
    wral
    #
    @6
    va
    cD
    wral
    #
    wa
    @12
    @3
    @6
    va
    cD
    r19.26
    @13
    @9
    @14
    @11
    @13
    vp
    cD
    @2
    @3
    vp
    cv
    #
    @2
    wcel
    va
    @15
    cD
    @0
    @15
    @2
    eleq1
    rspccv
    ssrdv
    @14
    va
    cD
    @5
    ciun
    #
    wfun
    #
    @11
    @14
    @16
    wrel
    #
    vx
    cv
    #
    vz
    cv
    #
    cop
    #
    @16
    wcel
    #
    @20
    vy
    cv
    wceq
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vx
    wal
    #
    @17
    @14
    @5
    wrel
    #
    va
    cD
    wral
    @18
    @6
    @28
    va
    cD
    @5
    funrel
    ralimi
    va
    cD
    @5
    reliun
    sylibr
    @14
    @21
    cF
    wcel
    #
    @19
    cD
    wcel
    #
    wa
    #
    @23
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vx
    wal
    @27
    @14
    @34
    vx
    @14
    @30
    @29
    @23
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    wi
    #
    @34
    @30
    @14
    @37
    @30
    @14
    wa
    cF
    @19
    csn
    #
    cres
    #
    wfun
    #
    @37
    @6
    @41
    va
    @19
    cD
    @0
    @19
    wceq
    #
    @5
    @40
    @42
    @4
    @39
    cF
    @0
    @19
    sneq
    reseq2d
    funeqd
    rspcva
    @41
    @40
    wrel
    #
    vw
    cv
    #
    @20
    cop
    #
    @40
    wcel
    #
    @23
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vw
    wal
    #
    wa
    @37
    vw
    vz
    vy
    @40
    dffun5
    @50
    @37
    @43
    @50
    @45
    @19
    @0
    cop
    #
    wceq
    #
    @51
    cF
    wcel
    #
    wa
    #
    va
    wex
    #
    @23
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vw
    wal
    @37
    @49
    @58
    vw
    @48
    @57
    vy
    @47
    @56
    vz
    @46
    @55
    @23
    va
    @45
    cF
    @19
    vx
    vex
    elsnres
    imbi1i
    albii
    exbii
    albii
    @58
    @37
    vw
    vx
    @44
    @19
    wceq
    #
    @57
    @36
    vy
    @59
    @56
    @35
    vz
    @59
    @29
    @55
    @23
    @59
    @29
    @55
    @59
    @29
    wa
    #
    @54
    va
    vz
    @0
    @20
    wceq
    #
    @60
    @54
    @61
    @60
    wa
    @52
    @53
    @60
    @61
    @52
    @59
    @61
    @52
    wi
    @29
    @61
    @20
    @0
    wceq
    #
    @59
    @52
    va
    vz
    equcom
    @59
    @62
    @52
    @44
    @20
    @19
    @0
    opeq12
    ex
    syl5bi
    adantr
    impcom
    @60
    @61
    @53
    @29
    @61
    @53
    wi
    @59
    @61
    @29
    @53
    @61
    @21
    @51
    cF
    @21
    @51
    wceq
    vz
    va
    @20
    @0
    @19
    opeq2
    equcoms
    eleq1d
    biimpcd
    adantl
    impcom
    jca
    ex
    spimev
    ex
    imim1d
    alimdv
    eximdv
    spimvw
    sylbi
    adantl
    sylbi
    syl
    expcom
    @34
    @30
    @35
    wi
    #
    vz
    wal
    #
    vy
    wex
    @30
    @36
    wi
    #
    vy
    wex
    @38
    @33
    @64
    vy
    @32
    @63
    vz
    @32
    @30
    @29
    wa
    @23
    wi
    @63
    @29
    @30
    @23
    ancomst
    @30
    @29
    @23
    impexp
    bitri
    albii
    exbii
    @64
    @65
    vy
    @30
    @35
    vz
    19.21v
    exbii
    @30
    @36
    vy
    19.37v
    3bitri
    sylibr
    alrimiv
    @26
    @34
    vx
    @25
    @33
    vy
    @24
    @32
    vz
    @22
    @31
    @23
    @22
    @21
    cF
    va
    cD
    @4
    ciun
    #
    cres
    #
    wcel
    @21
    @10
    wcel
    @31
    @16
    @67
    @21
    @67
    @16
    va
    cD
    @4
    cF
    resiun2
    #
    eqcomi
    eleq2i
    @67
    @10
    @21
    @66
    cD
    cF
    va
    cD
    iunid
    #
    reseq2i
    eleq2i
    @19
    @20
    cF
    cD
    vz
    vex
    opelres
    3bitri
    imbi1i
    albii
    exbii
    albii
    sylibr
    vx
    vz
    vy
    @16
    dffun5
    sylanbrc
    @11
    @67
    wfun
    @17
    @10
    @67
    cD
    @66
    cF
    @66
    cD
    @69
    eqcomi
    reseq2i
    funeqi
    @67
    @16
    @68
    funeqi
    bitri
    sylibr
    anim12i
    sylbi
    syl
end
