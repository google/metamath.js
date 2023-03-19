include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "cmdat.mm"
include "co.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "csymg.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "csn.mm"
include "cur.mm"
include "cop.mm"
include "wceq.mm"
include "eqid.mm"
include "mdetfval.mm"
include "a1i.mm"
include "mat0dimbas0.mm"
include "mpteq1d.mm"
include "cvv.mm"
include "0ex.mm"
include "ovex.mm"
include "oveq.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "fmptsng.mm"
include "sylancl.mm"
include "c0g.mm"
include "mpt0.mm"
include "gsum0.mm"
include "syl6eq.mm"
include "wa.mm"
include "ringidval.mm"
include "eqcomi.mm"
include "cfn.mm"
include "0fin.mm"
include "zrhcopsgnelbas.mm"
include "mp3an2.mm"
include "ringridm.mm"
include "syldan.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cevpm.mm"
include "simpl.mm"
include "c1.mm"
include "simpr.mm"
include "elsni.mm"
include "fveq2.mm"
include "psgn0fv0.mm"
include "syl.mm"
include "symgbas0.mm"
include "eleq2s.mm"
include "adantl.mm"
include "wb.mm"
include "psgnevpmb.mm"
include "mpbir2and.mm"
include "zrhpsgnevpm.mm"
include "syl3anc.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "ringidcl.mm"
include "eqidd.mm"
include "gsumsn.mm"
include "3eqtrd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtr3d.mm"

theorem mdet0pr
  let cR: class R
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x


  assert |- ( R e. Ring -> ( (/) maDet R ) = { <. (/) , ( 1r ` R ) >. } )

  proof
    cR
    crg
    wcel
    #
    c0
    cR
    cmdat
    co
    #
    vm
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cR
    vp
    c0
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    c0
    cpsgn
    cfv
    #
    ccom
    cfv
    #
    cR
    cmgp
    cfv
    #
    vx
    c0
    vx
    cv
    #
    @6
    cfv
    #
    @11
    vm
    cv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vm
    c0
    csn
    #
    @20
    cmpt
    #
    c0
    cR
    cur
    cfv
    #
    cop
    #
    csn
    #
    @1
    @21
    wceq
    @0
    vx
    @2
    @3
    @1
    @5
    cR
    @8
    @17
    @10
    vm
    c0
    @7
    vp
    @1
    eqid
    @2
    eqid
    @3
    eqid
    @5
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @17
    eqid
    #
    @10
    eqid
    #
    mdetfval
    a1i
    @0
    vm
    @3
    @22
    @20
    cR
    crg
    mat0dimbas0
    mpteq1d
    @0
    c0
    cR
    vp
    @5
    @9
    @10
    vx
    c0
    @12
    @11
    c0
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @17
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cop
    #
    csn
    #
    @23
    @26
    @0
    c0
    cvv
    wcel
    #
    @37
    cvv
    wcel
    @39
    @23
    wceq
    @40
    @0
    0ex
    a1i
    #
    cR
    @36
    cgsu
    ovex
    vm
    c0
    @20
    @37
    cvv
    cvv
    @13
    c0
    wceq
    #
    @19
    @36
    cR
    cgsu
    @42
    vp
    @5
    @18
    @35
    @42
    @16
    @34
    @9
    @17
    @42
    @15
    @33
    @10
    cgsu
    @42
    vx
    c0
    @14
    @32
    @12
    @11
    @13
    c0
    oveq
    mpteq2dv
    oveq2d
    oveq2d
    mpteq2dv
    oveq2d
    fmptsng
    sylancl
    @0
    @38
    @25
    @0
    @37
    @24
    c0
    @0
    @37
    cR
    vp
    @5
    @9
    @10
    c0g
    cfv
    #
    @17
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vp
    @5
    @9
    cmpt
    #
    cgsu
    co
    #
    @24
    @0
    @36
    @45
    cR
    cgsu
    @0
    vp
    @5
    @35
    @44
    @0
    @34
    @43
    @9
    @17
    @0
    @34
    @10
    c0
    cgsu
    co
    @43
    @0
    @33
    c0
    @10
    cgsu
    @33
    c0
    wceq
    @0
    vx
    @32
    mpt0
    a1i
    oveq2d
    @10
    @43
    @43
    eqid
    gsum0
    syl6eq
    oveq2d
    mpteq2dv
    oveq2d
    @0
    @45
    @46
    cR
    cgsu
    @0
    vp
    @5
    @44
    @9
    @0
    @6
    @5
    wcel
    #
    wa
    #
    @44
    @9
    @24
    @17
    co
    #
    @9
    @49
    @43
    @24
    @9
    @17
    @43
    @24
    wceq
    @49
    @24
    @43
    cR
    @24
    @10
    @31
    @24
    eqid
    #
    ringidval
    eqcomi
    a1i
    oveq2d
    @0
    @48
    @9
    cR
    cbs
    cfv
    #
    wcel
    #
    @50
    @9
    wceq
    @0
    c0
    cfn
    wcel
    #
    @48
    @53
    0fin
    @5
    @6
    cR
    @8
    c0
    @7
    @27
    @29
    @28
    zrhcopsgnelbas
    mp3an2
    @52
    cR
    @17
    @24
    @9
    @52
    eqid
    #
    @30
    @51
    ringridm
    syldan
    eqtrd
    mpteq2dva
    oveq2d
    @0
    @47
    cR
    vp
    @5
    @24
    cmpt
    #
    cgsu
    co
    cR
    vp
    @22
    @24
    cmpt
    #
    cgsu
    co
    #
    @24
    @0
    @46
    @56
    cR
    cgsu
    @0
    vp
    @5
    @9
    @24
    @49
    @0
    @54
    @6
    c0
    cevpm
    cfv
    wcel
    #
    @9
    @24
    wceq
    @0
    @48
    simpl
    @54
    @49
    0fin
    a1i
    #
    @49
    @59
    @48
    @6
    @8
    cfv
    #
    c1
    wceq
    #
    @0
    @48
    simpr
    @48
    @62
    @0
    @62
    @6
    @22
    @5
    @6
    @22
    wcel
    @6
    c0
    wceq
    #
    @62
    @6
    c0
    elsni
    @63
    @61
    c0
    @8
    cfv
    c1
    @6
    c0
    @8
    fveq2
    psgn0fv0
    syl6eq
    syl
    symgbas0
    eleq2s
    adantl
    @49
    @54
    @59
    @48
    @62
    wa
    wb
    @60
    c0
    @5
    @4
    @6
    @8
    @4
    eqid
    @27
    @29
    psgnevpmb
    syl
    mpbir2and
    cR
    @8
    @24
    @6
    c0
    @7
    @28
    @29
    @51
    zrhpsgnevpm
    syl3anc
    mpteq2dva
    oveq2d
    @0
    @56
    @57
    cR
    cgsu
    @0
    vp
    @5
    @22
    @24
    @5
    @22
    wceq
    @0
    symgbas0
    a1i
    mpteq1d
    oveq2d
    @0
    cR
    cmnd
    wcel
    @40
    @24
    @52
    wcel
    @58
    @24
    wceq
    cR
    ringmnd
    @41
    @52
    cR
    @24
    @55
    @51
    ringidcl
    @24
    @52
    @24
    vp
    cR
    c0
    cvv
    @55
    @63
    @24
    eqidd
    gsumsn
    syl3anc
    3eqtrd
    3eqtrd
    opeq2d
    sneqd
    eqtr3d
    3eqtrd
end
