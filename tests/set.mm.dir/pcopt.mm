include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cpco.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cphtpc.mm"
include "csn.mm"
include "cxp.mm"
include "fveq1i.mm"
include "cuni.mm"
include "simpr.mm"
include "wf.mm"
include "iiuni.mm"
include "eqid.mm"
include "cnf.mm"
include "adantr.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "elii1.mm"
include "iihalf1.mm"
include "sylbir.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "syl5eq.mm"
include "simplr.mm"
include "eqtr4d.mm"
include "ifeq1d.mm"
include "expr.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61d1.mm"
include "mpteq2dva.mm"
include "ctopon.mm"
include "w3a.mm"
include "ctop.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "pcoptcl.mm"
include "syl2anc.mm"
include "simp1d.mm"
include "simpl.mm"
include "pcoval.mm"
include "adantl.mm"
include "elii2.mm"
include "iihalf2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "iftrue.mm"
include "syl6eqel.mm"
include "pm2.61d2.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fvif.mm"
include "syl6eq.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "iitopon.mm"
include "cnmptid.mm"
include "cnmptc.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "dfii2.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "halflt1.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "simprl.mm"
include "oveq2d.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "syl6req.mm"
include "wss.mm"
include "retopon.mm"
include "iccssre.mm"
include "mp2an.mm"
include "resttopon.mm"
include "cnmpt2c.mm"
include "cnmpt1st.mm"
include "iihalf2cn.mm"
include "weq.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "cnmpt2pc.mm"
include "breq1.mm"
include "ifbieq2d.mm"
include "cnmpt12.mm"
include "id.mm"
include "syl6eqbr.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "1elunit.mm"
include "clt.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "mtbiri.mm"
include "2t1e2.mm"
include "2m1e1.mm"
include "eqtrd.mm"
include "1ex.mm"
include "reparpht.mm"
include "eqbrtrd.mm"

theorem pcopt
  let cP: class P
  let cF: class F
  let cJ: class J
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pcopt.1: |- P = ( ( 0 [,] 1 ) X. { Y } )


  assert |- ( ( F e. ( II Cn J ) /\ ( F ` 0 ) = Y ) -> ( P ( *p ` J ) F ) ( ~=ph ` J ) F )

  proof
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cc0
    cF
    cfv
    #
    cY
    wceq
    #
    wa
    #
    cP
    cF
    cJ
    cpco
    cfv
    co
    #
    cF
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cc0
    c2
    @7
    cmul
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    ccom
    #
    cF
    cJ
    cphtpc
    cfv
    @4
    vx
    @6
    @9
    @10
    cP
    cfv
    #
    @11
    cF
    cfv
    #
    cif
    #
    cmpt
    vx
    @6
    @9
    @2
    @16
    cif
    #
    cmpt
    @5
    @14
    @4
    vx
    @6
    @17
    @18
    @4
    @7
    @6
    wcel
    #
    wa
    @9
    @17
    @18
    wceq
    #
    @4
    @19
    @9
    @20
    @4
    @19
    @9
    wa
    #
    wa
    #
    @9
    @15
    @2
    @16
    @22
    @15
    cY
    @2
    @22
    @15
    @10
    @6
    cY
    csn
    cxp
    #
    cfv
    #
    cY
    @10
    cP
    @23
    pcopt.1
    fveq1i
    @4
    cY
    cJ
    cuni
    #
    wcel
    #
    @10
    @6
    wcel
    #
    @24
    cY
    wceq
    @21
    @4
    @2
    cY
    @25
    @1
    @3
    simpr
    @4
    @6
    @25
    cF
    wf
    #
    cc0
    @6
    wcel
    #
    @2
    @25
    wcel
    @1
    @28
    @3
    cF
    cii
    cJ
    @6
    @25
    iiuni
    @25
    eqid
    #
    cnf
    adantr
    #
    0elunit
    @6
    @25
    cc0
    cF
    ffvelrn
    sylancl
    eqeltrrd
    #
    @21
    @7
    cc0
    @8
    cicc
    co
    #
    wcel
    @27
    @7
    elii1
    @7
    iihalf1
    sylbir
    @6
    cY
    @10
    @25
    fvconst2g
    syl2an
    syl5eq
    @1
    @3
    @21
    simplr
    eqtr4d
    ifeq1d
    expr
    @9
    wn
    #
    @17
    @16
    @18
    @9
    @15
    @16
    iffalse
    @9
    @2
    @16
    iffalse
    eqtr4d
    pm2.61d1
    mpteq2dva
    @4
    vx
    cP
    cF
    cJ
    @4
    cP
    @0
    wcel
    #
    cc0
    cP
    cfv
    cY
    wceq
    #
    c1
    cP
    cfv
    cY
    wceq
    #
    @4
    cJ
    @25
    ctopon
    cfv
    wcel
    #
    @26
    @35
    @36
    @37
    w3a
    @4
    cJ
    ctop
    wcel
    #
    @38
    @1
    @39
    @3
    cF
    cii
    cJ
    cntop2
    adantr
    cJ
    @25
    @30
    toptopon
    sylib
    @32
    cP
    cJ
    @25
    cY
    pcopt.1
    pcoptcl
    syl2anc
    simp1d
    @1
    @3
    simpl
    #
    pcoval
    @4
    vx
    vy
    @6
    @6
    @12
    vy
    cv
    #
    cF
    cfv
    #
    @18
    @13
    cF
    @19
    @12
    @6
    wcel
    #
    @4
    @19
    @9
    @43
    @19
    @34
    @43
    @19
    @34
    wa
    #
    @12
    @11
    @6
    @34
    @12
    @11
    wceq
    #
    @19
    @9
    cc0
    @11
    iffalse
    #
    adantl
    @44
    @7
    @8
    c1
    cicc
    co
    #
    wcel
    @11
    @6
    wcel
    @7
    elii2
    @7
    iihalf2
    syl
    eqeltrd
    ex
    @9
    @12
    cc0
    @6
    @9
    cc0
    @11
    iftrue
    #
    0elunit
    syl6eqel
    pm2.61d2
    adantl
    @13
    @13
    wceq
    @4
    @13
    eqid
    #
    a1i
    @4
    vy
    @6
    @25
    cF
    @31
    feqmptd
    @41
    @12
    wceq
    @42
    @12
    cF
    cfv
    @18
    @41
    @12
    cF
    fveq2
    @9
    cc0
    @11
    cF
    fvif
    syl6eq
    fmptco
    3eqtr4d
    @4
    cF
    @13
    cJ
    @40
    @4
    vx
    vy
    vz
    @7
    cc0
    @41
    @8
    cle
    wbr
    #
    cc0
    c2
    @41
    cmul
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @12
    cii
    cii
    cii
    cii
    @6
    @6
    @6
    cii
    @6
    ctopon
    cfv
    wcel
    @4
    iitopon
    a1i
    #
    @4
    vx
    cii
    @6
    @54
    cnmptid
    @4
    vx
    cc0
    cii
    cii
    @6
    @6
    @54
    @54
    @29
    @4
    0elunit
    a1i
    #
    cnmptc
    @54
    @54
    @4
    vy
    vz
    cc0
    @8
    c1
    cc0
    cioo
    crn
    ctg
    cfv
    #
    @52
    cii
    cii
    @56
    @33
    crest
    co
    #
    @56
    @47
    crest
    co
    #
    cii
    @6
    @56
    eqid
    @57
    eqid
    @58
    eqid
    #
    dfii2
    cc0
    cr
    wcel
    #
    @4
    0re
    a1i
    c1
    cr
    wcel
    #
    @4
    1re
    a1i
    @8
    @6
    wcel
    #
    @4
    @62
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    @8
    c1
    cle
    wbr
    halfre
    cc0
    @8
    0re
    halfre
    halfgt0
    ltleii
    #
    @8
    c1
    halfre
    1re
    halflt1
    ltleii
    cc0
    c1
    @8
    0re
    1re
    elicc2i
    mpbir3an
    a1i
    @54
    @4
    @41
    @8
    wceq
    #
    vz
    cv
    #
    @6
    wcel
    #
    wa
    wa
    #
    @52
    c1
    c1
    cmin
    co
    cc0
    @68
    @51
    c1
    c1
    cmin
    @68
    @51
    c2
    @8
    cmul
    co
    c1
    @68
    @41
    @8
    c2
    cmul
    @4
    @65
    @67
    simprl
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    oveq1d
    1m1e0
    syl6req
    @4
    vy
    vz
    cc0
    @57
    cii
    cii
    @33
    @6
    @6
    @57
    @33
    ctopon
    cfv
    wcel
    #
    @4
    @56
    cr
    ctopon
    cfv
    wcel
    #
    @33
    cr
    wss
    #
    @69
    retopon
    @60
    @63
    @71
    0re
    halfre
    cc0
    @8
    iccssre
    mp2an
    @33
    @56
    cr
    resttopon
    mp2an
    a1i
    @54
    @54
    @55
    cnmpt2c
    @4
    vy
    vz
    vx
    @41
    @11
    @52
    @58
    cii
    @58
    cii
    @47
    @6
    @47
    @58
    @47
    ctopon
    cfv
    wcel
    #
    @4
    @70
    @47
    cr
    wss
    #
    @72
    retopon
    @63
    @61
    @73
    halfre
    1re
    @8
    c1
    iccssre
    mp2an
    @47
    @56
    cr
    resttopon
    mp2an
    a1i
    #
    @54
    @4
    vy
    vz
    @58
    cii
    @47
    @6
    @74
    @54
    cnmpt1st
    @74
    vx
    @47
    @11
    cmpt
    @58
    cii
    ccn
    co
    wcel
    @4
    vx
    @58
    @59
    iihalf2cn
    a1i
    vx
    vy
    weq
    @10
    @51
    c1
    cmin
    @7
    @41
    c2
    cmul
    oveq2
    oveq1d
    cnmpt21
    cnmpt2pc
    vy
    vx
    weq
    #
    @53
    @12
    wceq
    @66
    cc0
    wceq
    @75
    @50
    @9
    @52
    @11
    cc0
    @41
    @7
    @8
    cle
    breq1
    @75
    @51
    @10
    c1
    cmin
    @41
    @7
    c2
    cmul
    oveq2
    oveq1d
    ifbieq2d
    adantr
    cnmpt12
    @29
    cc0
    @13
    cfv
    cc0
    wceq
    @4
    0elunit
    vx
    cc0
    @12
    cc0
    @6
    @13
    @7
    cc0
    wceq
    #
    @9
    @12
    cc0
    wceq
    @76
    @7
    cc0
    @8
    cle
    @76
    id
    @64
    syl6eqbr
    @48
    syl
    @49
    c0ex
    fvmpt
    mp1i
    c1
    @6
    wcel
    c1
    @13
    cfv
    c1
    wceq
    @4
    1elunit
    vx
    c1
    @12
    c1
    @6
    @13
    @7
    c1
    wceq
    #
    @12
    @11
    c1
    @77
    @34
    @45
    @77
    @9
    c1
    @8
    cle
    wbr
    #
    @8
    c1
    clt
    wbr
    @78
    wn
    halflt1
    @8
    c1
    halfre
    1re
    ltnlei
    mpbi
    @7
    c1
    @8
    cle
    breq1
    mtbiri
    @46
    syl
    @77
    @11
    c2
    c1
    cmin
    co
    c1
    @77
    @10
    c2
    c1
    cmin
    @77
    @10
    c2
    c1
    cmul
    co
    c2
    @7
    c1
    c2
    cmul
    oveq2
    2t1e2
    syl6eq
    oveq1d
    2m1e1
    syl6eq
    eqtrd
    @49
    1ex
    fvmpt
    mp1i
    reparpht
    eqbrtrd
end
