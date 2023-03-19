include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cqqh.mm"
include "cz.mm"
include "ccnv.mm"
include "cui.mm"
include "cima.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "crn.mm"
include "csn.mm"
include "cdif.mm"
include "cq.mm"
include "cnumer.mm"
include "cdenom.mm"
include "cmpt.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "cur.mm"
include "eqid.mm"
include "qqhval.mm"
include "syl.mm"
include "eqidd.mm"
include "c0g.mm"
include "zrhunitpreima.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "rneqd.mm"
include "wrex.mm"
include "cab.mm"
include "copab.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfcv.mm"
include "wex.mm"
include "simpr.mm"
include "wne.mm"
include "zssq.mm"
include "simplrl.mm"
include "sseldi.mm"
include "simplrr.mm"
include "eldifad.mm"
include "wn.mm"
include "eldifbd.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "sylib.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "simplll.mm"
include "simpllr.mm"
include "w3a.mm"
include "qqhval2lem.mm"
include "eqcomd.mm"
include "syl23anc.mm"
include "ovex.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "simpl.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "spc2ev.mm"
include "syl12anc.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "imp.mm"
include "19.42vv.mm"
include "simprrl.mm"
include "qnumcl.mm"
include "cn.mm"
include "qdencl.mm"
include "nnzd.mm"
include "nnne0.mm"
include "nelsn.mm"
include "3syl.mm"
include "eldifd.mm"
include "simprl.mm"
include "qeqnumdivden.mm"
include "simprrr.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "impbida.mm"
include "abid.mm"
include "elopab.mm"
include "3bitr4g.mm"
include "eqrd.mm"
include "rnmpt2.mm"
include "df-mpt.mm"
include "3eqtr4g.mm"
include "3eqtrd.mm"

theorem qqhval2
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cL: class L
  let vq: setvar q
  let ve: setvar e
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )

  disjoint ./ q
  disjoint B q
  disjoint L q
  disjoint R q
  disjoint e q
  disjoint e s
  disjoint e x
  disjoint e y
  disjoint ./ e
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint s x
  disjoint s y
  disjoint ./ s
  disjoint x y
  disjoint ./ x
  disjoint ./ y
  disjoint B e
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint L e
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint R e
  disjoint R s
  disjoint R x
  disjoint R y
  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) = ( q e. QQ |-> ( ( L ` ( numer ` q ) ) ./ ( L ` ( denom ` q ) ) ) ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    cR
    cqqh
    cfv
    #
    vx
    vy
    cz
    cL
    ccnv
    cR
    cui
    cfv
    cima
    #
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    @5
    cL
    cfv
    #
    @6
    cL
    cfv
    #
    c.dv
    co
    #
    cop
    #
    cmpt2
    #
    crn
    #
    vx
    vy
    cz
    cz
    cc0
    csn
    #
    cdif
    #
    @11
    cmpt2
    #
    crn
    #
    vq
    cq
    vq
    cv
    #
    cnumer
    cfv
    #
    cL
    cfv
    #
    @18
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cmpt
    #
    @2
    cR
    cvv
    wcel
    #
    @3
    @13
    wceq
    @0
    @25
    @1
    cR
    cdr
    elex
    adantr
    vx
    vy
    c.dv
    cR
    cR
    cur
    cfv
    #
    cL
    qqhval2.1
    @26
    eqid
    qqhval2.2
    qqhval
    syl
    @2
    @12
    @16
    @2
    cz
    cz
    wceq
    @4
    @15
    wceq
    @12
    @16
    wceq
    @2
    cz
    eqidd
    cB
    cR
    cL
    cR
    c0g
    cfv
    #
    qqhval2.0
    qqhval2.2
    @27
    eqid
    zrhunitpreima
    vx
    vy
    cz
    @4
    cz
    @15
    @11
    mpt2eq12
    syl2anc
    rneqd
    @2
    ve
    cv
    #
    @11
    wceq
    #
    vy
    @15
    wrex
    vx
    cz
    wrex
    #
    ve
    cab
    #
    @18
    cq
    wcel
    #
    vs
    cv
    #
    @23
    wceq
    #
    wa
    #
    vq
    vs
    copab
    #
    @17
    @24
    @2
    ve
    @31
    @36
    @2
    ve
    nfv
    @30
    ve
    nfab1
    ve
    @36
    nfcv
    @2
    @30
    @28
    @18
    @33
    cop
    #
    wceq
    #
    @35
    wa
    #
    vs
    wex
    vq
    wex
    #
    @28
    @31
    wcel
    @28
    @36
    wcel
    @2
    @30
    @40
    @2
    @30
    @40
    @2
    @29
    @40
    vx
    vy
    cz
    @15
    @2
    @5
    cz
    wcel
    #
    @6
    @15
    wcel
    #
    wa
    #
    wa
    #
    @29
    @40
    @44
    @29
    wa
    #
    @29
    @7
    cq
    wcel
    #
    @10
    @7
    cnumer
    cfv
    #
    cL
    cfv
    #
    @7
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    wceq
    #
    @40
    @44
    @29
    simpr
    @45
    @5
    cq
    wcel
    @6
    cq
    wcel
    @6
    cc0
    wne
    #
    @46
    @45
    cz
    cq
    @5
    zssq
    @2
    @41
    @42
    @29
    simplrl
    #
    sseldi
    @45
    cz
    cq
    @6
    zssq
    @45
    @6
    cz
    @14
    @2
    @41
    @42
    @29
    simplrr
    #
    eldifad
    #
    sseldi
    @45
    @6
    @14
    wcel
    #
    wn
    @53
    @45
    @6
    cz
    @14
    @55
    eldifbd
    @57
    @6
    cc0
    vy
    cc0
    velsn
    necon3bbii
    sylib
    #
    @5
    @6
    qdivcl
    syl3anc
    @45
    @0
    @1
    @41
    @6
    cz
    wcel
    #
    @53
    @52
    @0
    @1
    @43
    @29
    simplll
    @0
    @1
    @43
    @29
    simpllr
    @54
    @56
    @58
    @2
    @41
    @59
    @53
    w3a
    wa
    @51
    @10
    cB
    c.dv
    cR
    cL
    @5
    @6
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhval2lem
    eqcomd
    syl23anc
    @39
    @29
    @46
    @52
    wa
    #
    wa
    vq
    vs
    @7
    @10
    @5
    @6
    cdiv
    ovex
    @8
    @9
    c.dv
    ovex
    @18
    @7
    wceq
    #
    @33
    @10
    wceq
    #
    wa
    #
    @38
    @29
    @35
    @60
    @63
    @37
    @11
    @28
    @18
    @33
    @7
    @10
    opeq12
    eqeq2d
    @63
    @32
    @46
    @34
    @52
    @63
    @18
    @7
    cq
    @61
    @62
    simpl
    #
    eleq1d
    @63
    @33
    @10
    @23
    @51
    @61
    @62
    simpr
    @63
    @20
    @48
    @22
    @50
    c.dv
    @63
    @19
    @47
    cL
    @63
    @18
    @7
    cnumer
    @64
    fveq2d
    fveq2d
    @63
    @21
    @49
    cL
    @63
    @18
    @7
    cdenom
    @64
    fveq2d
    fveq2d
    oveq12d
    eqeq12d
    anbi12d
    anbi12d
    spc2ev
    syl12anc
    ex
    rexlimdvva
    imp
    @2
    @40
    wa
    @2
    @39
    wa
    #
    vs
    wex
    vq
    wex
    @30
    @2
    @39
    vq
    vs
    19.42vv
    @65
    @30
    vq
    vs
    @65
    @19
    cz
    wcel
    #
    @21
    @15
    wcel
    @28
    @19
    @21
    cdiv
    co
    #
    @23
    cop
    #
    wceq
    #
    @30
    @65
    @32
    @66
    @2
    @38
    @32
    @34
    simprrl
    #
    @18
    qnumcl
    syl
    @65
    @21
    cz
    @14
    @65
    @21
    @65
    @32
    @21
    cn
    wcel
    #
    @70
    @18
    qdencl
    syl
    #
    nnzd
    @65
    @71
    @21
    cc0
    wne
    @21
    @14
    wcel
    wn
    @72
    @21
    nnne0
    @21
    cc0
    nelsn
    3syl
    eldifd
    @65
    @28
    @37
    @68
    @2
    @38
    @35
    simprl
    @65
    @18
    @67
    @33
    @23
    @65
    @32
    @18
    @67
    wceq
    @70
    @18
    qeqnumdivden
    syl
    @2
    @38
    @32
    @34
    simprrr
    opeq12d
    eqtrd
    @29
    @69
    @28
    @19
    @6
    cdiv
    co
    #
    @20
    @9
    c.dv
    co
    #
    cop
    #
    wceq
    vx
    vy
    @19
    @21
    cz
    @15
    @5
    @19
    wceq
    #
    @11
    @75
    @28
    @76
    @7
    @73
    @10
    @74
    @5
    @19
    @6
    cdiv
    oveq1
    @76
    @8
    @20
    @9
    c.dv
    @5
    @19
    cL
    fveq2
    oveq1d
    opeq12d
    eqeq2d
    @6
    @21
    wceq
    #
    @75
    @68
    @28
    @77
    @73
    @67
    @74
    @23
    @6
    @21
    @19
    cdiv
    oveq2
    @77
    @9
    @22
    @20
    c.dv
    @6
    @21
    cL
    fveq2
    oveq2d
    opeq12d
    eqeq2d
    rspc2ev
    syl3anc
    exlimivv
    sylbir
    impbida
    @30
    ve
    abid
    @35
    vq
    vs
    @28
    elopab
    3bitr4g
    eqrd
    vx
    vy
    ve
    cz
    @15
    @11
    @16
    @16
    eqid
    rnmpt2
    vq
    vs
    cq
    @23
    df-mpt
    3eqtr4g
    3eqtrd
end
