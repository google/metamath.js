include "wac.mm"
include "cv.mm"
include "wss.mm"
include "cdm.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "df-ac.mm"
include "wel.mm"
include "copab.mm"
include "cuni.mm"
include "cxp.mm"
include "vex.mm"
include "vuniex.mm"
include "xpex.mm"
include "simpl.mm"
include "elunii.mm"
include "ancoms.mm"
include "jca.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "wceq.mm"
include "sseq2.mm"
include "dmeq.mm"
include "fneq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "spcv.mm"
include "csn.mm"
include "cima.mm"
include "wb.mm"
include "fndm.mm"
include "eleq2.mm"
include "cab.mm"
include "dmopab.mm"
include "eleq2i.mm"
include "weq.mm"
include "elequ1.mm"
include "elab.mm"
include "19.42v.mm"
include "n0.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "3bitrri.mm"
include "syl6rbbr.mm"
include "syl.mm"
include "adantl.mm"
include "wfun.mm"
include "fnfun.mm"
include "funfvima3.mm"
include "sylan2.mm"
include "sylbid.mm"
include "imp.mm"
include "ibar.mm"
include "abbi2dv.mm"
include "wbr.mm"
include "cvv.mm"
include "imasng.mm"
include "ax-mp.mm"
include "anbi2d.mm"
include "eqid.mm"
include "brab.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "ad2antrl.mm"
include "mpbid.mm"
include "exp32.mm"
include "ralrimiv.mm"
include "eximi.mm"
include "alrimiv.mm"
include "cmpt.mm"
include "aceq3lem.mm"
include "impbii.mm"
include "bitri.mm"

theorem dfac3
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint f x
  disjoint f z
  disjoint x z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f u
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- ( CHOICE <-> A. x E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) )

  proof
    wac
    vf
    cv
    #
    vy
    cv
    #
    wss
    #
    @0
    @1
    cdm
    #
    wfn
    #
    wa
    #
    vf
    wex
    #
    vy
    wal
    #
    vz
    cv
    #
    c0
    wne
    #
    @8
    @0
    cfv
    #
    @8
    wcel
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vf
    wex
    #
    vx
    wal
    #
    vy
    vf
    df-ac
    @7
    @16
    @7
    @15
    vx
    @7
    @0
    vw
    vx
    wel
    #
    vv
    vw
    wel
    #
    wa
    #
    vw
    vv
    copab
    #
    wss
    #
    @0
    @20
    cdm
    #
    wfn
    #
    wa
    #
    vf
    wex
    #
    @15
    @6
    @25
    vy
    @20
    @20
    @13
    @13
    cuni
    #
    cxp
    #
    @13
    @26
    vx
    vex
    vx
    vuniex
    xpex
    @20
    @17
    vv
    cv
    #
    @26
    wcel
    #
    wa
    #
    vw
    vv
    copab
    @27
    @19
    @30
    vw
    vv
    @19
    @17
    @29
    @17
    @18
    simpl
    @18
    @17
    @29
    @28
    vw
    cv
    #
    @13
    elunii
    ancoms
    jca
    ssopab2i
    vw
    vv
    @13
    @26
    df-xp
    sseqtr4i
    ssexi
    @1
    @20
    wceq
    #
    @5
    @24
    vf
    @32
    @2
    @21
    @4
    @23
    @1
    @20
    @0
    sseq2
    @32
    @3
    @22
    @0
    @1
    @20
    dmeq
    fneq2d
    anbi12d
    exbidv
    spcv
    @24
    @14
    vf
    @24
    @12
    vz
    @13
    @24
    vz
    vx
    wel
    #
    @9
    @11
    @24
    @33
    @9
    wa
    #
    wa
    @10
    @20
    @8
    csn
    cima
    #
    wcel
    #
    @11
    @24
    @34
    @36
    @24
    @34
    @8
    @0
    cdm
    #
    wcel
    #
    @36
    @23
    @34
    @38
    wb
    #
    @21
    @23
    @37
    @22
    wceq
    #
    @39
    @22
    @0
    fndm
    @40
    @38
    @8
    @22
    wcel
    #
    @34
    @37
    @22
    @8
    eleq2
    @41
    @8
    @19
    vv
    wex
    #
    vw
    cab
    #
    wcel
    @33
    vv
    vz
    wel
    #
    wa
    #
    vv
    wex
    #
    @34
    @22
    @43
    @8
    @19
    vw
    vv
    dmopab
    eleq2i
    @42
    @46
    vw
    @8
    vz
    vex
    #
    vw
    vz
    weq
    #
    @19
    @45
    vv
    @48
    @17
    @33
    @18
    @44
    vw
    vz
    vx
    elequ1
    @31
    @8
    @28
    eleq2
    anbi12d
    #
    exbidv
    elab
    @46
    @33
    @44
    vv
    wex
    #
    wa
    @34
    @33
    @44
    vv
    19.42v
    @9
    @50
    @33
    vv
    @8
    n0
    anbi2i
    bitr4i
    3bitrri
    syl6rbbr
    syl
    adantl
    @23
    @21
    @0
    wfun
    #
    @38
    @36
    wi
    #
    @22
    @0
    fnfun
    @51
    @21
    @52
    @8
    @0
    @20
    funfvima3
    ancoms
    sylan2
    sylbid
    imp
    @33
    @36
    @11
    wb
    @24
    @9
    @33
    @35
    @8
    @10
    @33
    @8
    @33
    vu
    vz
    wel
    #
    wa
    #
    vu
    cab
    #
    @35
    @33
    @54
    vu
    @8
    @33
    @53
    ibar
    abbi2dv
    @35
    @8
    vu
    cv
    #
    @20
    wbr
    #
    vu
    cab
    #
    @55
    @8
    cvv
    wcel
    @35
    @58
    wceq
    @47
    vu
    @8
    cvv
    @20
    imasng
    ax-mp
    @57
    @54
    vu
    @19
    @45
    @54
    vw
    vv
    @8
    @56
    @20
    @47
    vu
    vex
    @49
    vv
    vu
    weq
    @44
    @53
    @33
    vv
    vu
    vz
    elequ1
    anbi2d
    @20
    eqid
    brab
    abbii
    eqtri
    syl6reqr
    eleq2d
    ad2antrl
    mpbid
    exp32
    ralrimiv
    eximi
    syl
    alrimiv
    @16
    @6
    vy
    vx
    vy
    vz
    vw
    vu
    vf
    vw
    @3
    @31
    @56
    @1
    wbr
    vu
    cab
    @0
    cfv
    cmpt
    #
    @59
    eqid
    aceq3lem
    alrimiv
    impbii
    bitri
end
