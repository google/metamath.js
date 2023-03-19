include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "clmhm.mm"
include "co.mm"
include "wf.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "lmhmf.mm"
include "lmhmsca.mm"
include "cghm.mm"
include "lmghm.mm"
include "adantr.mm"
include "lmhmlmod1.mm"
include "simpr1.mm"
include "simpr2.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "ghmlin.mm"
include "lmhmlin.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "ralrimivvva.mm"
include "3jca.mm"
include "adantl.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "anim12i.mm"
include "wi.mm"
include "cur.mm"
include "crg.mm"
include "lmodring.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "ringidcl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "rspcv.mm"
include "3syl.mm"
include "simplll.mm"
include "simprl.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "simpllr.mm"
include "simplrl.mm"
include "ffvelrnd.mm"
include "eqtr3d.mm"
include "2ralbidva.mm"
include "sylibd.mm"
include "exp32.mm"
include "3imp2.mm"
include "jca.mm"
include "isghm.mm"
include "sylanbrc.mm"
include "c0g.mm"
include "ghmid.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "grpidcl.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "simprr.mm"
include "grprid.mm"
include "simplr3.mm"
include "cbs.mm"
include "simplr2.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "simplr1.mm"
include "ralimdvva.mm"
include "3exp2.mm"
include "com45.mm"
include "mpd.mm"
include "wb.mm"
include "islmhm3.mm"
include "mpbir3and.mm"
include "impbida.mm"

theorem islmhm2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  assume islmhm2.b: |- B = ( Base ` S )
  assume islmhm2.c: |- C = ( Base ` T )
  assume islmhm2.k: |- K = ( Scalar ` S )
  assume islmhm2.l: |- L = ( Scalar ` T )
  assume islmhm2.e: |- E = ( Base ` K )
  assume islmhm2.p: |- .+ = ( +g ` S )
  assume islmhm2.q: |- .+^ = ( +g ` T )
  assume islmhm2.m: |- .x. = ( .s ` S )
  assume islmhm2.n: |- .X. = ( .s ` T )

  disjoint x y
  disjoint x z
  disjoint .+^ x
  disjoint y z
  disjoint .+^ y
  disjoint .+^ z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint .x. x
  disjoint .x. z
  disjoint .X. x
  disjoint .X. z
  assert |- ( ( S e. LMod /\ T e. LMod ) -> ( F e. ( S LMHom T ) <-> ( F : B --> C /\ L = K /\ A. x e. E A. y e. B A. z e. B ( F ` ( ( x .x. y ) .+ z ) ) = ( ( x .X. ( F ` y ) ) .+^ ( F ` z ) ) ) ) )

  proof
    cS
    clmod
    wcel
    #
    cT
    clmod
    wcel
    #
    wa
    #
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cB
    cC
    cF
    wf
    #
    cL
    cK
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    vz
    cv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @6
    @7
    cF
    cfv
    #
    c.xp
    co
    #
    @9
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cE
    wral
    #
    w3a
    #
    @3
    @20
    @2
    @3
    @4
    @5
    @19
    cB
    cC
    cS
    cT
    cF
    islmhm2.b
    islmhm2.c
    lmhmf
    cS
    cT
    cF
    cK
    cL
    islmhm2.k
    islmhm2.l
    lmhmsca
    @3
    @16
    vx
    vy
    vz
    cE
    cB
    cB
    @3
    @6
    cE
    wcel
    #
    @7
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    w3a
    #
    wa
    #
    @11
    @8
    cF
    cfv
    #
    @14
    c.pd
    co
    #
    @15
    @25
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @8
    cB
    wcel
    #
    @23
    @11
    @27
    wceq
    @3
    @28
    @24
    cS
    cT
    cF
    lmghm
    adantr
    @25
    @0
    @21
    @22
    @29
    @3
    @0
    @24
    cS
    cT
    cF
    lmhmlmod1
    adantr
    @3
    @21
    @22
    @23
    simpr1
    @3
    @21
    @22
    @23
    simpr2
    @6
    c.x
    cK
    cE
    cB
    cS
    @7
    islmhm2.b
    islmhm2.k
    islmhm2.m
    islmhm2.e
    lmodvscl
    #
    syl3anc
    @3
    @21
    @22
    @23
    simpr3
    c.pl
    c.pd
    cS
    cT
    @8
    cF
    @9
    cB
    islmhm2.b
    islmhm2.p
    islmhm2.q
    ghmlin
    syl3anc
    @25
    @26
    @13
    @14
    c.pd
    @3
    @21
    @22
    @26
    @13
    wceq
    #
    @23
    cE
    cS
    cT
    c.x
    c.xp
    cB
    cF
    cK
    @6
    @7
    islmhm2.k
    islmhm2.e
    islmhm2.b
    islmhm2.m
    islmhm2.n
    lmhmlin
    3adant3r3
    oveq1d
    eqtrd
    ralrimivvva
    3jca
    adantl
    @2
    @20
    wa
    #
    @3
    @28
    @5
    @31
    vy
    cB
    wral
    vx
    cE
    wral
    #
    @32
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    wa
    #
    @4
    @7
    @9
    c.pl
    co
    #
    cF
    cfv
    #
    @12
    @14
    c.pd
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    @28
    @2
    @36
    @20
    @0
    @34
    @1
    @35
    cS
    lmodgrp
    #
    cT
    lmodgrp
    #
    anim12i
    adantr
    @32
    @4
    @41
    @2
    @4
    @5
    @19
    simpr1
    @2
    @4
    @5
    @19
    @41
    @2
    @4
    @5
    @19
    @41
    wi
    @2
    @4
    @5
    wa
    #
    wa
    #
    @19
    cK
    cur
    cfv
    #
    @7
    c.x
    co
    #
    @9
    c.pl
    co
    #
    cF
    cfv
    #
    @46
    @12
    c.xp
    co
    #
    @14
    c.pd
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    @41
    @45
    cK
    crg
    wcel
    #
    @46
    cE
    wcel
    @19
    @53
    wi
    @0
    @54
    @1
    @44
    cK
    cS
    islmhm2.k
    lmodring
    ad2antrr
    cE
    cK
    @46
    islmhm2.e
    @46
    eqid
    #
    ringidcl
    @18
    @53
    vx
    @46
    cE
    @6
    @46
    wceq
    #
    @16
    @52
    vy
    vz
    cB
    cB
    @56
    @11
    @49
    @15
    @51
    @56
    @10
    @48
    cF
    @56
    @8
    @47
    @9
    c.pl
    @6
    @46
    @7
    c.x
    oveq1
    oveq1d
    fveq2d
    @56
    @13
    @50
    @14
    c.pd
    @6
    @46
    @12
    c.xp
    oveq1
    oveq1d
    eqeq12d
    2ralbidv
    rspcv
    3syl
    @45
    @52
    @40
    vy
    vz
    cB
    cB
    @45
    @22
    @23
    wa
    #
    wa
    #
    @49
    @38
    @51
    @39
    @58
    @48
    @37
    cF
    @58
    @47
    @7
    @9
    c.pl
    @58
    @0
    @22
    @47
    @7
    wceq
    @0
    @1
    @44
    @57
    simplll
    @45
    @22
    @23
    simprl
    #
    c.x
    @46
    cK
    cB
    cS
    @7
    islmhm2.b
    islmhm2.k
    islmhm2.m
    @55
    lmodvs1
    syl2anc
    oveq1d
    fveq2d
    @58
    @50
    @12
    @14
    c.pd
    @58
    cL
    cur
    cfv
    #
    @12
    c.xp
    co
    #
    @50
    @12
    @58
    @60
    @46
    @12
    c.xp
    @58
    cL
    cK
    cur
    @2
    @4
    @5
    @57
    simplrr
    fveq2d
    oveq1d
    @58
    @1
    @12
    cC
    wcel
    #
    @61
    @12
    wceq
    @0
    @1
    @44
    @57
    simpllr
    @58
    cB
    cC
    @7
    cF
    @2
    @4
    @5
    @57
    simplrl
    @59
    ffvelrnd
    c.xp
    @60
    cL
    cC
    cT
    @12
    islmhm2.c
    islmhm2.l
    islmhm2.n
    @60
    eqid
    lmodvs1
    syl2anc
    eqtr3d
    oveq1d
    eqeq12d
    2ralbidva
    sylibd
    exp32
    3imp2
    jca
    vz
    vy
    c.pl
    c.pd
    cS
    cT
    cF
    cB
    cC
    islmhm2.b
    islmhm2.c
    islmhm2.p
    islmhm2.q
    isghm
    sylanbrc
    #
    @2
    @4
    @5
    @19
    simpr2
    @32
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    @33
    @32
    @28
    @67
    @63
    cS
    cT
    cF
    @64
    @66
    @64
    eqid
    #
    @66
    eqid
    #
    ghmid
    syl
    @2
    @4
    @5
    @19
    @67
    @33
    wi
    @2
    @4
    @5
    @67
    @19
    @33
    @2
    @4
    @5
    @67
    @19
    @33
    wi
    @2
    @4
    @5
    @67
    w3a
    #
    wa
    #
    @17
    @31
    vx
    vy
    cE
    cB
    @71
    @21
    @22
    wa
    #
    wa
    #
    @17
    @8
    @64
    c.pl
    co
    #
    cF
    cfv
    #
    @13
    @65
    c.pd
    co
    #
    wceq
    #
    @31
    @73
    @34
    @64
    cB
    wcel
    @17
    @77
    wi
    @0
    @34
    @1
    @70
    @72
    @42
    ad3antrrr
    #
    cB
    cS
    @64
    islmhm2.b
    @68
    grpidcl
    @16
    @77
    vz
    @64
    cB
    @9
    @64
    wceq
    #
    @11
    @75
    @15
    @76
    @79
    @10
    @74
    cF
    @9
    @64
    @8
    c.pl
    oveq2
    fveq2d
    @79
    @14
    @65
    @13
    c.pd
    @9
    @64
    cF
    fveq2
    oveq2d
    eqeq12d
    rspcv
    3syl
    @73
    @75
    @26
    @76
    @13
    @73
    @74
    @8
    cF
    @73
    @34
    @29
    @74
    @8
    wceq
    @78
    @73
    @0
    @21
    @22
    @29
    @0
    @1
    @70
    @72
    simplll
    @71
    @21
    @22
    simprl
    #
    @71
    @21
    @22
    simprr
    #
    @30
    syl3anc
    cB
    c.pl
    cS
    @8
    @64
    islmhm2.b
    islmhm2.p
    @68
    grprid
    syl2anc
    fveq2d
    @73
    @76
    @13
    @66
    c.pd
    co
    #
    @13
    @73
    @65
    @66
    @13
    c.pd
    @4
    @5
    @67
    @2
    @72
    simplr3
    oveq2d
    @73
    @35
    @13
    cC
    wcel
    #
    @82
    @13
    wceq
    @73
    @1
    @35
    @0
    @1
    @70
    @72
    simpllr
    #
    @43
    syl
    @73
    @1
    @6
    cL
    cbs
    cfv
    #
    wcel
    @62
    @83
    @84
    @73
    @6
    cE
    @85
    @80
    @73
    @85
    cK
    cbs
    cfv
    cE
    @73
    cL
    cK
    cbs
    @4
    @5
    @67
    @2
    @72
    simplr2
    fveq2d
    islmhm2.e
    syl6eqr
    eleqtrrd
    @73
    cB
    cC
    @7
    cF
    @4
    @5
    @67
    @2
    @72
    simplr1
    @81
    ffvelrnd
    @6
    c.xp
    cL
    @85
    cC
    cT
    @12
    islmhm2.c
    islmhm2.l
    islmhm2.n
    @85
    eqid
    lmodvscl
    syl3anc
    cC
    c.pd
    cT
    @13
    @66
    islmhm2.c
    islmhm2.q
    @69
    grprid
    syl2anc
    eqtrd
    eqeq12d
    sylibd
    ralimdvva
    3exp2
    com45
    3imp2
    mpd
    @2
    @3
    @28
    @5
    @33
    w3a
    wb
    @20
    vx
    vy
    cE
    cS
    cT
    c.x
    c.xp
    cB
    cF
    cK
    cL
    islmhm2.k
    islmhm2.l
    islmhm2.e
    islmhm2.b
    islmhm2.m
    islmhm2.n
    islmhm3
    adantr
    mpbir3and
    impbida
end
