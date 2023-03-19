include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cpco.mm"
include "cc0.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cphtpc.mm"
include "cmin.mm"
include "wn.mm"
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
include "1elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "elii2.mm"
include "iihalf2.mm"
include "syl.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "syl5eq.mm"
include "simplr.mm"
include "eqtr4d.mm"
include "anassrs.mm"
include "ifeq2da.mm"
include "mpteq2dva.mm"
include "simpl.mm"
include "ctopon.mm"
include "w3a.mm"
include "ctop.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "pcoptcl.mm"
include "syl2anc.mm"
include "simp1d.mm"
include "pcoval.mm"
include "iftrue.mm"
include "adantl.mm"
include "elii1.mm"
include "iihalf1.mm"
include "sylbir.mm"
include "eqeltrd.mm"
include "ex.mm"
include "iffalse.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fvif.mm"
include "syl6eq.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmptid.mm"
include "0elunit.mm"
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
include "wss.mm"
include "retopon.mm"
include "iccssre.mm"
include "mp2an.mm"
include "resttopon.mm"
include "cnmpt1st.mm"
include "iihalf1cn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "cnmpt2c.mm"
include "cnmpt2pc.mm"
include "breq1.mm"
include "ifbieq1d.mm"
include "cnmpt12.mm"
include "id.mm"
include "syl6eqbr.mm"
include "2t0e0.mm"
include "eqtrd.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "clt.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "mtbiri.mm"
include "1ex.mm"
include "reparpht.mm"
include "eqbrtrd.mm"

theorem pcopt2
  let cP: class P
  let cF: class F
  let cJ: class J
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pcopt.1: |- P = ( ( 0 [,] 1 ) X. { Y } )


  assert |- ( ( F e. ( II Cn J ) /\ ( F ` 1 ) = Y ) -> ( F ( *p ` J ) P ) ( ~=ph ` J ) F )

  proof
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    c1
    cF
    cfv
    #
    cY
    wceq
    #
    wa
    #
    cF
    cP
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
    c2
    @7
    cmul
    co
    #
    c1
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
    cF
    cfv
    #
    @10
    c1
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    vx
    @6
    @9
    @14
    @2
    cif
    #
    cmpt
    @5
    @13
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
    @16
    @2
    @14
    @4
    @19
    @9
    wn
    #
    @16
    @2
    wceq
    @4
    @19
    @20
    wa
    #
    wa
    #
    @16
    cY
    @2
    @22
    @16
    @15
    @6
    cY
    csn
    cxp
    #
    cfv
    #
    cY
    @15
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
    @15
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
    c1
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
    1elunit
    @6
    @25
    c1
    cF
    ffvelrn
    sylancl
    eqeltrrd
    #
    @21
    @7
    @8
    c1
    cicc
    co
    #
    wcel
    @27
    @7
    elii2
    @7
    iihalf2
    syl
    @6
    cY
    @15
    @25
    fvconst2g
    syl2an
    syl5eq
    @1
    @3
    @21
    simplr
    eqtr4d
    anassrs
    ifeq2da
    mpteq2dva
    @4
    vx
    cF
    cP
    cJ
    @1
    @3
    simpl
    #
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
    pcoval
    @4
    vx
    vy
    @6
    @6
    @11
    vy
    cv
    #
    cF
    cfv
    #
    @18
    @12
    cF
    @19
    @11
    @6
    wcel
    #
    @4
    @19
    @9
    @42
    @19
    @9
    @42
    @19
    @9
    wa
    #
    @11
    @10
    @6
    @9
    @11
    @10
    wceq
    #
    @19
    @9
    @10
    c1
    iftrue
    #
    adantl
    @43
    @7
    cc0
    @8
    cicc
    co
    #
    wcel
    @10
    @6
    wcel
    @7
    elii1
    @7
    iihalf1
    sylbir
    eqeltrd
    ex
    @20
    @11
    c1
    @6
    @9
    @10
    c1
    iffalse
    #
    1elunit
    syl6eqel
    pm2.61d1
    adantl
    @4
    @12
    eqidd
    @4
    vy
    @6
    @25
    cF
    @31
    feqmptd
    @40
    @11
    wceq
    @41
    @11
    cF
    cfv
    @18
    @40
    @11
    cF
    fveq2
    @9
    @10
    c1
    cF
    fvif
    syl6eq
    fmptco
    3eqtr4d
    @4
    cF
    @12
    cJ
    @34
    @4
    vx
    vy
    vz
    @7
    cc0
    @40
    @8
    cle
    wbr
    #
    c2
    @40
    cmul
    co
    #
    c1
    cif
    #
    @11
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
    @51
    cnmptid
    @4
    vx
    cc0
    cii
    cii
    @6
    @6
    @51
    @51
    cc0
    @6
    wcel
    #
    @4
    0elunit
    a1i
    cnmptc
    @51
    @51
    @4
    vy
    vz
    cc0
    @8
    c1
    @49
    cioo
    crn
    ctg
    cfv
    #
    c1
    cii
    cii
    @53
    @46
    crest
    co
    #
    @53
    @33
    crest
    co
    #
    cii
    @6
    @53
    eqid
    @54
    eqid
    #
    @55
    eqid
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
    @59
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
    @51
    @4
    @40
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
    @49
    c2
    @8
    cmul
    co
    c1
    @65
    @40
    @8
    c2
    cmul
    @4
    @62
    @64
    simprl
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    @4
    vy
    vz
    vx
    @40
    @10
    @49
    @54
    cii
    @54
    cii
    @46
    @6
    @46
    @54
    @46
    ctopon
    cfv
    wcel
    #
    @4
    @53
    cr
    ctopon
    cfv
    wcel
    #
    @46
    cr
    wss
    #
    @66
    retopon
    @57
    @60
    @68
    0re
    halfre
    cc0
    @8
    iccssre
    mp2an
    @46
    @53
    cr
    resttopon
    mp2an
    a1i
    #
    @51
    @4
    vy
    vz
    @54
    cii
    @46
    @6
    @69
    @51
    cnmpt1st
    @69
    vx
    @46
    @10
    cmpt
    @54
    cii
    ccn
    co
    wcel
    @4
    vx
    @54
    @56
    iihalf1cn
    a1i
    @7
    @40
    c2
    cmul
    oveq2
    cnmpt21
    @4
    vy
    vz
    c1
    @55
    cii
    cii
    @33
    @6
    @6
    @55
    @33
    ctopon
    cfv
    wcel
    #
    @4
    @67
    @33
    cr
    wss
    #
    @70
    retopon
    @60
    @58
    @71
    halfre
    1re
    @8
    c1
    iccssre
    mp2an
    @33
    @53
    cr
    resttopon
    mp2an
    a1i
    @51
    @51
    @29
    @4
    1elunit
    a1i
    cnmpt2c
    cnmpt2pc
    @40
    @7
    wceq
    #
    @50
    @11
    wceq
    @63
    cc0
    wceq
    @72
    @48
    @9
    @49
    @10
    c1
    @40
    @7
    @8
    cle
    breq1
    @40
    @7
    c2
    cmul
    oveq2
    ifbieq1d
    adantr
    cnmpt12
    @52
    cc0
    @12
    cfv
    cc0
    wceq
    @4
    0elunit
    vx
    cc0
    @11
    cc0
    @6
    @12
    @7
    cc0
    wceq
    #
    @11
    @10
    cc0
    @73
    @9
    @44
    @73
    @7
    cc0
    @8
    cle
    @73
    id
    @61
    syl6eqbr
    @45
    syl
    @73
    @10
    c2
    cc0
    cmul
    co
    cc0
    @7
    cc0
    c2
    cmul
    oveq2
    2t0e0
    syl6eq
    eqtrd
    @12
    eqid
    #
    c0ex
    fvmpt
    mp1i
    @29
    c1
    @12
    cfv
    c1
    wceq
    @4
    1elunit
    vx
    c1
    @11
    c1
    @6
    @12
    @7
    c1
    wceq
    #
    @20
    @11
    c1
    wceq
    @75
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
    @76
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
    @47
    syl
    @74
    1ex
    fvmpt
    mp1i
    reparpht
    eqbrtrd
end
