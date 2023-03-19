include "cfield.mm"
include "wcel.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "cui.mm"
include "ccur.mm"
include "cfrlm.mm"
include "clindf.mm"
include "wbr.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "mat0dimbas0.mm"
include "sylan9eq.mm"
include "eleq2d.mm"
include "elsni.mm"
include "syl6bi.mm"
include "imdistanda.mm"
include "impcom.mm"
include "cdr.mm"
include "crg.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "drngring.mm"
include "cur.mm"
include "eqid.mm"
include "mat0dimid.mm"
include "cfn.mm"
include "0fin.mm"
include "matring.mm"
include "mpan.mm"
include "1unit.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "3syl.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "f0.mm"
include "dm0.mm"
include "feq2i.mm"
include "mpbir.mm"
include "rzal.mm"
include "ax-mp.mm"
include "cvv.mm"
include "ovex.mm"
include "islindf.mm"
include "mp2an.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "2thd.mm"
include "eleq12.mm"
include "sylan2.mm"
include "cureq.mm"
include "cop.mm"
include "copab.mm"
include "cmpt.mm"
include "df-cur.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "breqan12d.mm"
include "bibi12d.mm"
include "biimparc.mm"
include "sylan.mm"
include "anassrs.mm"
include "sylancom.mm"
include "wne.mm"
include "cmdat.mm"
include "simprbi.mm"
include "matunit.mm"
include "adantr.mm"
include "drngunit.mm"
include "mdetcl.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "cxp.mm"
include "wi.mm"
include "matrcl.mm"
include "simpld.mm"
include "pm4.71i.mm"
include "cmap.mm"
include "xpfi.mm"
include "anidms.mm"
include "frlmfibas.mm"
include "matbas.mm"
include "ancoms.mm"
include "eqtrd.mm"
include "fvex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "adantl.mm"
include "bitr3d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "syl5bb.mm"
include "biimpd.mm"
include "imdistani.mm"
include "anass.mm"
include "sylibr.mm"
include "eldifsn.mm"
include "matunitlindflem1.mm"
include "necon1ad.mm"
include "sylan2br.mm"
include "sylbid.mm"
include "matunitlindflem2.mm"
include "impbid.mm"
include "bitrd.mm"
include "pm2.61dane.mm"

theorem matunitlindf
  let cR: class R
  let cI: class I
  let cM: class M
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( R e. Field /\ M e. ( Base ` ( I Mat R ) ) ) -> ( M e. ( Unit ` ( I Mat R ) ) <-> curry M LIndF ( R freeLMod I ) ) )

  proof
    cR
    cfield
    wcel
    #
    cM
    cI
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    cM
    @1
    cui
    cfv
    #
    wcel
    #
    cM
    ccur
    #
    cR
    cI
    cfrlm
    co
    #
    clindf
    wbr
    #
    wb
    #
    cI
    c0
    @4
    cI
    c0
    wceq
    #
    @0
    cM
    c0
    wceq
    #
    wa
    #
    @10
    @11
    @4
    @13
    @11
    @0
    @3
    @12
    @11
    @0
    wa
    #
    @3
    cM
    c0
    csn
    #
    wcel
    @12
    @14
    @2
    @15
    cM
    @11
    @0
    @2
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    @15
    @11
    @1
    @16
    cbs
    cI
    c0
    cR
    cmat
    oveq1
    #
    fveq2d
    cR
    cfield
    mat0dimbas0
    sylan9eq
    eleq2d
    cM
    c0
    elsni
    syl6bi
    imdistanda
    impcom
    @0
    @12
    @11
    @10
    @0
    c0
    @16
    cui
    cfv
    #
    wcel
    #
    c0
    cR
    c0
    cfrlm
    co
    #
    clindf
    wbr
    #
    wb
    #
    @12
    @11
    wa
    #
    @10
    @0
    @19
    @21
    @0
    cR
    cdr
    wcel
    #
    cR
    crg
    wcel
    #
    @19
    @0
    @24
    cR
    ccrg
    wcel
    #
    cR
    isfld
    #
    simplbi
    #
    cR
    drngring
    @25
    @16
    cur
    cfv
    #
    c0
    @18
    @16
    cR
    @16
    eqid
    #
    mat0dimid
    @25
    @16
    crg
    wcel
    #
    @29
    @18
    wcel
    c0
    cfn
    wcel
    #
    @25
    @31
    0fin
    @16
    cR
    c0
    @30
    matring
    mpan
    @16
    @18
    @29
    @18
    eqid
    @29
    eqid
    1unit
    syl
    eqeltrrd
    3syl
    @21
    @0
    @21
    c0
    cdm
    #
    @20
    cbs
    cfv
    #
    c0
    wf
    #
    vy
    cv
    #
    vx
    cv
    #
    c0
    cfv
    @20
    cvsca
    cfv
    #
    co
    c0
    @33
    @37
    csn
    cdif
    cima
    @20
    clspn
    cfv
    #
    cfv
    wcel
    wn
    vy
    @20
    csca
    cfv
    #
    cbs
    cfv
    #
    @40
    c0g
    cfv
    #
    csn
    cdif
    wral
    #
    vx
    @33
    wral
    #
    @35
    c0
    @34
    c0
    wf
    @34
    f0
    @33
    c0
    @34
    c0
    dm0
    feq2i
    mpbir
    @33
    c0
    wceq
    @44
    dm0
    @43
    vx
    @33
    rzal
    ax-mp
    @20
    cvv
    wcel
    @32
    @21
    @35
    @44
    wa
    wb
    cR
    c0
    cfrlm
    ovex
    0fin
    vx
    @34
    @40
    @38
    vy
    c0
    @39
    @41
    @20
    cfn
    cvv
    @42
    @34
    eqid
    @38
    eqid
    @39
    eqid
    @40
    eqid
    @41
    eqid
    @42
    eqid
    islindf
    mp2an
    mpbir2an
    a1i
    2thd
    @23
    @10
    @22
    @23
    @6
    @19
    @9
    @21
    @11
    @12
    @5
    @18
    wceq
    @6
    @19
    wb
    @11
    @1
    @16
    cui
    @17
    fveq2d
    cM
    c0
    @5
    @18
    eleq12
    sylan2
    @12
    @11
    @7
    c0
    @8
    @20
    clindf
    @12
    @7
    c0
    ccur
    #
    c0
    cM
    c0
    cureq
    @45
    vx
    @33
    cdm
    #
    @37
    @36
    cop
    vz
    cv
    c0
    wbr
    vy
    vz
    copab
    #
    cmpt
    #
    vx
    c0
    @47
    cmpt
    #
    c0
    vx
    vy
    vz
    c0
    df-cur
    @46
    c0
    wceq
    @48
    @49
    wceq
    @46
    @33
    c0
    @33
    c0
    dm0
    dmeqi
    dm0
    eqtri
    vx
    @46
    c0
    @47
    mpteq1
    ax-mp
    vx
    @47
    mpt0
    3eqtri
    syl6eq
    cI
    c0
    cR
    cfrlm
    oveq2
    breqan12d
    bibi12d
    biimparc
    sylan
    anassrs
    sylancom
    @4
    cI
    c0
    wne
    #
    wa
    #
    @6
    cM
    cI
    cR
    cmdat
    co
    #
    cfv
    #
    cR
    cui
    cfv
    #
    wcel
    #
    @9
    @4
    @6
    @55
    wb
    #
    @50
    @0
    @26
    @3
    @56
    @0
    @24
    @26
    @27
    simprbi
    #
    @1
    @2
    @52
    cR
    @5
    cM
    cI
    @54
    @1
    eqid
    #
    @52
    eqid
    #
    @2
    eqid
    #
    @5
    eqid
    @54
    eqid
    #
    matunit
    sylan
    adantr
    @51
    @55
    @9
    @51
    @55
    @53
    cR
    c0g
    cfv
    #
    wne
    #
    @9
    @4
    @55
    @63
    wb
    @50
    @4
    @55
    @53
    cR
    cbs
    cfv
    #
    wcel
    #
    @63
    wa
    #
    @63
    @0
    @55
    @66
    wb
    #
    @3
    @0
    @24
    @67
    @28
    @64
    cR
    @54
    @53
    @62
    @64
    eqid
    #
    @61
    @62
    eqid
    drngunit
    syl
    adantr
    @4
    @65
    @63
    @0
    @26
    @3
    @65
    @57
    @1
    @2
    @52
    cR
    @64
    cM
    cI
    @59
    @58
    @60
    @68
    mdetcl
    sylan
    biantrurd
    bitr4d
    adantr
    @4
    @0
    cI
    cI
    cxp
    #
    @64
    cM
    wf
    #
    wa
    #
    cI
    cfn
    wcel
    #
    wa
    #
    @50
    @63
    @9
    wi
    #
    @4
    @0
    @70
    @72
    wa
    #
    wa
    @73
    @0
    @3
    @75
    @0
    @3
    @75
    @3
    @3
    @72
    wa
    @0
    @75
    @3
    @72
    @3
    @72
    cR
    cvv
    wcel
    @1
    @2
    cR
    cI
    cM
    @58
    @60
    matrcl
    simpld
    pm4.71i
    @0
    @72
    @3
    @70
    @0
    @72
    @3
    @70
    wb
    @0
    @72
    wa
    #
    cM
    @64
    @69
    cmap
    co
    #
    wcel
    #
    @3
    @70
    @76
    @77
    @2
    cM
    @76
    @77
    cR
    @69
    cfrlm
    co
    #
    cbs
    cfv
    #
    @2
    @72
    @0
    @69
    cfn
    wcel
    #
    @77
    @80
    wceq
    @72
    @81
    cI
    cI
    xpfi
    anidms
    #
    cR
    @79
    @69
    @64
    cfield
    @79
    eqid
    #
    @68
    frlmfibas
    sylan2
    @72
    @0
    @80
    @2
    wceq
    @1
    cR
    @79
    cI
    cfield
    @58
    @83
    matbas
    ancoms
    eqtrd
    eleq2d
    @72
    @78
    @70
    wb
    #
    @0
    @72
    @64
    cvv
    wcel
    @81
    @84
    cR
    cbs
    fvex
    @82
    @64
    @69
    cM
    cvv
    cfn
    elmapg
    sylancr
    adantl
    bitr3d
    ex
    pm5.32rd
    syl5bb
    biimpd
    imdistani
    @0
    @70
    @72
    anass
    sylibr
    @71
    @72
    @50
    @74
    @72
    @50
    wa
    @71
    cI
    cfn
    @15
    cdif
    wcel
    #
    @74
    cI
    cfn
    c0
    eldifsn
    @71
    @85
    wa
    @9
    @53
    @62
    cR
    cI
    cM
    matunitlindflem1
    necon1ad
    sylan2br
    anassrs
    sylan
    sylbid
    @51
    @9
    @55
    cR
    cI
    cM
    matunitlindflem2
    ex
    impbid
    bitrd
    pm2.61dane
end
