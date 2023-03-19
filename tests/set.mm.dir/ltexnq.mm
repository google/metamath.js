include "cnq.mm"
include "wcel.mm"
include "cltq.mm"
include "wbr.mm"
include "cv.mm"
include "cplq.mm"
include "co.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "ltrelnq.mm"
include "brel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "clti.mm"
include "ordpinq.mm"
include "cpli.mm"
include "cnpi.mm"
include "wrex.mm"
include "wb.mm"
include "cxp.mm"
include "elpqn.mm"
include "adantr.mm"
include "xp1st.mm"
include "syl.mm"
include "adantl.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "ltexpi.mm"
include "cop.mm"
include "cerq.mm"
include "cplpq.mm"
include "wrel.mm"
include "relxp.mm"
include "ad2antrr.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "oveq1d.mm"
include "simpr.mm"
include "addpipq.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "distrpi.mm"
include "fvex.mm"
include "mulcompi.mm"
include "mulasspi.mm"
include "caov12.mm"
include "oveq12i.mm"
include "eqtr2i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "eqcomi.mm"
include "a1i.mm"
include "opeq12d.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "fveq2.mm"
include "adderpq.mm"
include "nqerid.mm"
include "syl5eqr.mm"
include "ceq.mm"
include "mulcanenq.mm"
include "syl3anc.mm"
include "ad2antlr.mm"
include "breqtrrd.mm"
include "opelxpi.mm"
include "nqereq.mm"
include "mpbid.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "syld.mm"
include "eqeq1d.mm"
include "spcev.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "mpcom.mm"
include "eleq1.mm"
include "biimparc.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "ltaddnq.mm"
include "3syl.mm"
include "breqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "impbid2.mm"

theorem ltexnq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( B e. Q. -> ( A <Q B <-> E. x ( A +Q x ) = B ) )

  proof
    cB
    cnq
    wcel
    #
    cA
    cB
    cltq
    wbr
    #
    cA
    vx
    cv
    #
    cplq
    co
    #
    cB
    wceq
    #
    vx
    wex
    #
    cA
    cnq
    wcel
    #
    @0
    wa
    #
    @1
    @5
    cA
    cB
    cnq
    cnq
    cltq
    ltrelnq
    brel
    @7
    @1
    cA
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    cB
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    @5
    cA
    cB
    ordpinq
    @7
    @14
    @10
    vy
    cv
    #
    cpli
    co
    #
    @13
    wceq
    #
    vy
    cnpi
    wrex
    #
    @5
    @7
    @10
    cnpi
    wcel
    #
    @13
    cnpi
    wcel
    #
    @14
    @18
    wb
    @7
    @8
    cnpi
    wcel
    #
    @9
    cnpi
    wcel
    #
    @19
    @7
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @21
    @6
    @24
    @0
    cA
    elpqn
    #
    adantr
    #
    cA
    cnpi
    cnpi
    xp1st
    syl
    #
    @7
    cB
    @23
    wcel
    #
    @22
    @0
    @28
    @6
    cB
    elpqn
    #
    adantl
    #
    cB
    cnpi
    cnpi
    xp2nd
    syl
    #
    @8
    @9
    mulclpi
    syl2anc
    @7
    @11
    cnpi
    wcel
    #
    @12
    cnpi
    wcel
    #
    @20
    @7
    @28
    @32
    @30
    cB
    cnpi
    cnpi
    xp1st
    syl
    #
    @7
    @24
    @33
    @26
    cA
    cnpi
    cnpi
    xp2nd
    syl
    #
    @11
    @12
    mulclpi
    syl2anc
    vy
    @10
    @13
    ltexpi
    syl2anc
    @7
    @17
    @5
    vy
    cnpi
    @7
    @15
    cnpi
    wcel
    #
    wa
    #
    @17
    cA
    @15
    @12
    @9
    cmi
    co
    #
    cop
    #
    cerq
    cfv
    #
    cplq
    co
    #
    cB
    wceq
    #
    @5
    @37
    @17
    cA
    @39
    cplpq
    co
    #
    @12
    @12
    cmi
    co
    #
    @11
    cmi
    co
    #
    @44
    @9
    cmi
    co
    #
    cop
    #
    wceq
    #
    @42
    @37
    @43
    @8
    @38
    cmi
    co
    #
    @15
    @12
    cmi
    co
    #
    cpli
    co
    #
    @12
    @38
    cmi
    co
    #
    cop
    #
    wceq
    @17
    @48
    @37
    @43
    @8
    @12
    cop
    #
    @39
    cplpq
    co
    #
    @53
    @37
    cA
    @54
    @39
    cplpq
    @37
    @23
    wrel
    #
    @24
    cA
    @54
    wceq
    cnpi
    cnpi
    relxp
    #
    @6
    @24
    @0
    @36
    @25
    ad2antrr
    cA
    @23
    1st2nd
    sylancr
    oveq1d
    @37
    @21
    @33
    @36
    @38
    cnpi
    wcel
    #
    @55
    @53
    wceq
    @7
    @21
    @36
    @27
    adantr
    @7
    @33
    @36
    @35
    adantr
    @7
    @36
    simpr
    @7
    @58
    @36
    @7
    @33
    @22
    @58
    @35
    @31
    @12
    @9
    mulclpi
    syl2anc
    adantr
    @8
    @12
    @15
    @38
    addpipq
    syl22anc
    eqtrd
    @17
    @53
    @47
    @43
    @17
    @51
    @45
    @52
    @46
    @17
    @12
    @16
    cmi
    co
    #
    @12
    @13
    cmi
    co
    #
    @51
    @45
    @16
    @13
    @12
    cmi
    oveq2
    @59
    @12
    @10
    cmi
    co
    #
    @12
    @15
    cmi
    co
    #
    cpli
    co
    @51
    @12
    @10
    @15
    distrpi
    @61
    @49
    @62
    @50
    cpli
    vx
    vy
    vz
    @12
    @8
    @9
    cmi
    cA
    c2nd
    fvex
    cA
    c1st
    fvex
    cB
    c2nd
    fvex
    @2
    @15
    mulcompi
    @2
    @15
    vz
    cv
    mulasspi
    caov12
    @12
    @15
    mulcompi
    oveq12i
    eqtr2i
    @45
    @12
    @12
    @11
    cmi
    co
    #
    cmi
    co
    @60
    @12
    @12
    @11
    mulasspi
    @63
    @13
    @12
    cmi
    @12
    @11
    mulcompi
    oveq2i
    eqtri
    3eqtr4g
    @52
    @46
    wceq
    @17
    @46
    @52
    @12
    @12
    @9
    mulasspi
    eqcomi
    a1i
    opeq12d
    eqeq2d
    syl5ibcom
    @48
    @43
    cerq
    cfv
    #
    @47
    cerq
    cfv
    #
    wceq
    @37
    @42
    @43
    @47
    cerq
    fveq2
    @37
    @64
    @41
    @65
    cB
    @37
    @64
    cA
    cerq
    cfv
    #
    @40
    cplq
    co
    @41
    cA
    @39
    adderpq
    @37
    @66
    cA
    @40
    cplq
    @6
    @66
    cA
    wceq
    @0
    @36
    cA
    nqerid
    ad2antrr
    oveq1d
    syl5eqr
    @37
    @65
    cB
    cerq
    cfv
    #
    cB
    @37
    @47
    cB
    ceq
    wbr
    #
    @65
    @67
    wceq
    #
    @37
    @47
    @11
    @9
    cop
    #
    cB
    ceq
    @37
    @44
    cnpi
    wcel
    #
    @32
    @22
    @47
    @70
    ceq
    wbr
    @7
    @71
    @36
    @7
    @33
    @33
    @71
    @35
    @35
    @12
    @12
    mulclpi
    syl2anc
    adantr
    #
    @7
    @32
    @36
    @34
    adantr
    #
    @7
    @22
    @36
    @31
    adantr
    #
    @44
    @11
    @9
    mulcanenq
    syl3anc
    @37
    @56
    @28
    cB
    @70
    wceq
    @57
    @0
    @28
    @6
    @36
    @29
    ad2antlr
    #
    cB
    @23
    1st2nd
    sylancr
    breqtrrd
    @37
    @47
    @23
    wcel
    #
    @28
    @68
    @69
    wb
    @37
    @45
    cnpi
    wcel
    #
    @46
    cnpi
    wcel
    #
    @76
    @37
    @71
    @32
    @77
    @72
    @73
    @44
    @11
    mulclpi
    syl2anc
    @37
    @71
    @22
    @78
    @72
    @74
    @44
    @9
    mulclpi
    syl2anc
    @45
    @46
    cnpi
    cnpi
    opelxpi
    syl2anc
    @75
    @47
    cB
    nqereq
    syl2anc
    mpbid
    @0
    @67
    cB
    wceq
    @6
    @36
    cB
    nqerid
    ad2antlr
    eqtrd
    eqeq12d
    syl5ib
    syld
    @4
    @42
    vx
    @40
    @39
    cerq
    fvex
    @2
    @40
    wceq
    @3
    @41
    cB
    @2
    @40
    cA
    cplq
    oveq2
    eqeq1d
    spcev
    syl6
    rexlimdva
    sylbid
    sylbid
    mpcom
    @0
    @4
    @1
    vx
    @0
    @4
    @1
    @0
    @4
    wa
    #
    cA
    @3
    cB
    cltq
    @79
    @3
    cnq
    wcel
    #
    @6
    @2
    cnq
    wcel
    wa
    cA
    @3
    cltq
    wbr
    @4
    @80
    @0
    @3
    cB
    cnq
    eleq1
    biimparc
    cA
    @2
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    cA
    @2
    ltaddnq
    3syl
    @0
    @4
    simpr
    breqtrd
    ex
    exlimdv
    impbid2
end
