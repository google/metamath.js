include "csconn.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cpconn.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wi.mm"
include "cii.mm"
include "ccn.mm"
include "wral.mm"
include "sconnpconn.mm"
include "txpconn.mm"
include "syl2an.mm"
include "c1st.mm"
include "cuni.mm"
include "cres.mm"
include "ccom.mm"
include "cphtpy.mm"
include "wex.mm"
include "c2nd.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "simpll.mm"
include "simprl.mm"
include "ctopon.mm"
include "ctop.mm"
include "sconntop.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "ad2antlr.mm"
include "tx1cn.mm"
include "syl2anc.mm"
include "cnco.mm"
include "simprr.mm"
include "fveq2d.mm"
include "wf.mm"
include "iitopon.mm"
include "a1i.mm"
include "txtopon.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "1elunit.mm"
include "3eqtr4d.mm"
include "sconnpht.mm"
include "isphtpc.mm"
include "simp3d.mm"
include "n0.mm"
include "simplr.mm"
include "tx2cn.mm"
include "eeanv.mm"
include "adantr.mm"
include "txsconnlem.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "expr.mm"
include "ralrimiva.mm"
include "issconn.mm"
include "sylanbrc.mm"

theorem txsconn
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( R e. SConn /\ S e. SConn ) -> ( R tX S ) e. SConn )

  proof
    cR
    csconn
    wcel
    #
    cS
    csconn
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    cpconn
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    c1
    @5
    cfv
    #
    wceq
    #
    @5
    cc0
    c1
    cicc
    co
    #
    @6
    csn
    cxp
    @3
    cphtpc
    cfv
    wbr
    #
    wi
    #
    vf
    cii
    @3
    ccn
    co
    #
    wral
    @3
    csconn
    wcel
    @0
    cR
    cpconn
    wcel
    cS
    cpconn
    wcel
    @4
    @1
    cR
    sconnpconn
    cS
    sconnpconn
    cR
    cS
    txpconn
    syl2an
    @2
    @11
    vf
    @12
    @2
    @5
    @12
    wcel
    #
    @8
    @10
    @2
    @13
    @8
    wa
    #
    wa
    #
    vg
    cv
    #
    c1st
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    cres
    #
    @5
    ccom
    #
    @9
    cc0
    @21
    cfv
    #
    csn
    cxp
    #
    cR
    cphtpy
    cfv
    co
    #
    wcel
    #
    vg
    wex
    #
    vh
    cv
    #
    c2nd
    @19
    cres
    #
    @5
    ccom
    #
    @9
    cc0
    @29
    cfv
    #
    csn
    cxp
    #
    cS
    cphtpy
    cfv
    co
    #
    wcel
    #
    vh
    wex
    #
    @10
    @15
    @24
    c0
    wne
    #
    @26
    @15
    @21
    cii
    cR
    ccn
    co
    #
    wcel
    #
    @23
    @36
    wcel
    #
    @35
    @15
    @21
    @23
    cR
    cphtpc
    cfv
    wbr
    #
    @37
    @38
    @35
    w3a
    @15
    @0
    @37
    @22
    c1
    @21
    cfv
    #
    wceq
    @39
    @0
    @1
    @14
    simpll
    @15
    @13
    @20
    @3
    cR
    ccn
    co
    wcel
    #
    @37
    @2
    @13
    @8
    simprl
    #
    @15
    cR
    @17
    ctopon
    cfv
    wcel
    #
    cS
    @18
    ctopon
    cfv
    wcel
    #
    @41
    @15
    cR
    ctop
    wcel
    #
    @43
    @0
    @45
    @1
    @14
    cR
    sconntop
    ad2antrr
    #
    cR
    @17
    @17
    eqid
    toptopon
    sylib
    #
    @15
    cS
    ctop
    wcel
    #
    @44
    @1
    @48
    @0
    @14
    cS
    sconntop
    ad2antlr
    #
    cS
    @18
    @18
    eqid
    toptopon
    sylib
    #
    cR
    cS
    @17
    @18
    tx1cn
    syl2anc
    @5
    @20
    cii
    @3
    cR
    cnco
    syl2anc
    @15
    @6
    @20
    cfv
    #
    @7
    @20
    cfv
    #
    @22
    @40
    @15
    @6
    @7
    @20
    @2
    @13
    @8
    simprr
    #
    fveq2d
    @15
    @9
    @19
    @5
    wf
    #
    cc0
    @9
    wcel
    #
    @22
    @51
    wceq
    @15
    cii
    @9
    ctopon
    cfv
    wcel
    #
    @3
    @19
    ctopon
    cfv
    wcel
    #
    @13
    @54
    @56
    @15
    iitopon
    a1i
    @15
    @43
    @44
    @57
    @47
    @50
    cR
    cS
    @17
    @18
    txtopon
    syl2anc
    @42
    @5
    cii
    @3
    @9
    @19
    cnf2
    syl3anc
    #
    0elunit
    @9
    @19
    cc0
    @20
    @5
    fvco3
    sylancl
    @15
    @54
    c1
    @9
    wcel
    #
    @40
    @52
    wceq
    @58
    1elunit
    @9
    @19
    c1
    @20
    @5
    fvco3
    sylancl
    3eqtr4d
    @21
    cR
    sconnpht
    syl3anc
    @21
    @23
    cR
    isphtpc
    sylib
    simp3d
    vg
    @24
    n0
    sylib
    @15
    @32
    c0
    wne
    #
    @34
    @15
    @29
    cii
    cS
    ccn
    co
    #
    wcel
    #
    @31
    @61
    wcel
    #
    @60
    @15
    @29
    @31
    cS
    cphtpc
    cfv
    wbr
    #
    @62
    @63
    @60
    w3a
    @15
    @1
    @62
    @30
    c1
    @29
    cfv
    #
    wceq
    @64
    @0
    @1
    @14
    simplr
    @15
    @13
    @28
    @3
    cS
    ccn
    co
    wcel
    #
    @62
    @42
    @15
    @43
    @44
    @66
    @47
    @50
    cR
    cS
    @17
    @18
    tx2cn
    syl2anc
    @5
    @28
    cii
    @3
    cS
    cnco
    syl2anc
    @15
    @6
    @28
    cfv
    #
    @7
    @28
    cfv
    #
    @30
    @65
    @15
    @6
    @7
    @28
    @53
    fveq2d
    @15
    @54
    @55
    @30
    @67
    wceq
    @58
    0elunit
    @9
    @19
    cc0
    @28
    @5
    fvco3
    sylancl
    @15
    @54
    @59
    @65
    @68
    wceq
    @58
    1elunit
    @9
    @19
    c1
    @28
    @5
    fvco3
    sylancl
    3eqtr4d
    @29
    cS
    sconnpht
    syl3anc
    @29
    @31
    cS
    isphtpc
    sylib
    simp3d
    vh
    @32
    n0
    sylib
    @26
    @34
    wa
    @25
    @33
    wa
    #
    vh
    wex
    vg
    wex
    @15
    @10
    @25
    @33
    vg
    vh
    eeanv
    @15
    @69
    @10
    vg
    vh
    @15
    @69
    @10
    @15
    @69
    wa
    @21
    @29
    cR
    cS
    @5
    @16
    @27
    @15
    @45
    @69
    @46
    adantr
    @15
    @48
    @69
    @49
    adantr
    @15
    @13
    @69
    @42
    adantr
    @21
    eqid
    @29
    eqid
    @15
    @25
    @33
    simprl
    @15
    @25
    @33
    simprr
    txsconnlem
    ex
    exlimdvv
    syl5bir
    mp2and
    expr
    ralrimiva
    vf
    @3
    issconn
    sylanbrc
end
