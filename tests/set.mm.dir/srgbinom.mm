include "csrg.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "simpr1.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "mulg0.mm"
include "syl.mm"
include "simpr2.mm"
include "cur.mm"
include "srgidcl.mm"
include "ancli.mm"
include "adantr.mm"
include "srglidm.mm"
include "mulg1.mm"
include "eqtrd.mm"
include "wb.mm"
include "ringidval.mm"
include "id.mm"
include "ax-mp.mm"
include "sylib.mm"
include "csn.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "a1i.mm"
include "mpteq1d.mm"
include "cmnd.mm"
include "cvv.mm"
include "srgmnd.mm"
include "c0ex.mm"
include "syl5eqelr.mm"
include "eqeltrd.mm"
include "0nn0.mm"
include "bcn0.mm"
include "syl6eq.mm"
include "0m0e0.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "mndcl.mm"
include "3eqtr4rd.mm"
include "simprl.mm"
include "adantl.mm"
include "simprr3.mm"
include "simpl.mm"
include "srgbinomlem.mm"
include "exp31.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expd.mm"
include "impcom.mm"
include "imp.mm"

theorem srgbinom
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  assume srgbinom.s: |- S = ( Base ` R )
  assume srgbinom.m: |- .X. = ( .r ` R )
  assume srgbinom.t: |- .x. = ( .g ` R )
  assume srgbinom.a: |- .+ = ( +g ` R )
  assume srgbinom.g: |- G = ( mulGrp ` R )
  assume srgbinom.e: |- .^ = ( .g ` G )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint R k
  disjoint S k
  disjoint .x. k
  disjoint .^ k
  disjoint .X. k
  disjoint .+ k
  disjoint A n
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint B n
  disjoint B x
  disjoint N n
  disjoint N x
  disjoint R n
  disjoint R x
  disjoint S n
  disjoint S x
  disjoint .x. n
  disjoint .x. x
  disjoint .^ n
  disjoint .^ x
  disjoint .X. n
  disjoint .X. x
  disjoint .+ n
  disjoint .+ x
  assert |- ( ( ( R e. SRing /\ N e. NN0 ) /\ ( A e. S /\ B e. S /\ ( A .X. B ) = ( B .X. A ) ) ) -> ( N .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  proof
    cR
    csrg
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cB
    c.xp
    co
    cB
    cA
    c.xp
    co
    wceq
    #
    w3a
    #
    cN
    cA
    cB
    c.pl
    co
    #
    c.ex
    co
    #
    cR
    vk
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    cN
    @9
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @9
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    @1
    @0
    @5
    @18
    wi
    @1
    @0
    @5
    @18
    @0
    @5
    wa
    #
    vx
    cv
    #
    @6
    c.ex
    co
    #
    cR
    vk
    cc0
    @20
    cfz
    co
    #
    @20
    @9
    cbc
    co
    #
    @20
    @9
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @13
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @19
    cc0
    @6
    c.ex
    co
    #
    cR
    vk
    cc0
    cc0
    cfz
    co
    #
    cc0
    @9
    cbc
    co
    #
    cc0
    @9
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @13
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @19
    vn
    cv
    #
    @6
    c.ex
    co
    #
    cR
    vk
    cc0
    @41
    cfz
    co
    #
    @41
    @9
    cbc
    co
    #
    @41
    @9
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @13
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @19
    @41
    c1
    caddc
    co
    #
    @6
    c.ex
    co
    #
    cR
    vk
    cc0
    @52
    cfz
    co
    #
    @52
    @9
    cbc
    co
    #
    @52
    @9
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @13
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @19
    @18
    wi
    vx
    vn
    cN
    @20
    cc0
    wceq
    #
    @30
    @40
    @19
    @63
    @21
    @31
    @29
    @39
    @20
    cc0
    @6
    c.ex
    oveq1
    @63
    @28
    @38
    cR
    cgsu
    @63
    vk
    @22
    @27
    @32
    @37
    @20
    cc0
    cc0
    cfz
    oveq2
    @63
    @23
    @33
    @26
    @36
    c.x
    @20
    cc0
    @9
    cbc
    oveq1
    @63
    @25
    @35
    @13
    c.xp
    @63
    @24
    @34
    cA
    c.ex
    @20
    cc0
    @9
    cmin
    oveq1
    oveq1d
    oveq1d
    oveq12d
    mpteq12dv
    oveq2d
    eqeq12d
    imbi2d
    @20
    @41
    wceq
    #
    @30
    @51
    @19
    @64
    @21
    @42
    @29
    @50
    @20
    @41
    @6
    c.ex
    oveq1
    @64
    @28
    @49
    cR
    cgsu
    @64
    vk
    @22
    @27
    @43
    @48
    @20
    @41
    cc0
    cfz
    oveq2
    @64
    @23
    @44
    @26
    @47
    c.x
    @20
    @41
    @9
    cbc
    oveq1
    @64
    @25
    @46
    @13
    c.xp
    @64
    @24
    @45
    cA
    c.ex
    @20
    @41
    @9
    cmin
    oveq1
    oveq1d
    oveq1d
    oveq12d
    mpteq12dv
    oveq2d
    eqeq12d
    imbi2d
    @20
    @52
    wceq
    #
    @30
    @62
    @19
    @65
    @21
    @53
    @29
    @61
    @20
    @52
    @6
    c.ex
    oveq1
    @65
    @28
    @60
    cR
    cgsu
    @65
    vk
    @22
    @27
    @54
    @59
    @20
    @52
    cc0
    cfz
    oveq2
    @65
    @23
    @55
    @26
    @58
    c.x
    @20
    @52
    @9
    cbc
    oveq1
    @65
    @25
    @57
    @13
    c.xp
    @65
    @24
    @56
    cA
    c.ex
    @20
    @52
    @9
    cmin
    oveq1
    oveq1d
    oveq1d
    oveq12d
    mpteq12dv
    oveq2d
    eqeq12d
    imbi2d
    @20
    cN
    wceq
    #
    @30
    @18
    @19
    @66
    @21
    @7
    @29
    @17
    @20
    cN
    @6
    c.ex
    oveq1
    @66
    @28
    @16
    cR
    cgsu
    @66
    vk
    @22
    @27
    @8
    @15
    @20
    cN
    cc0
    cfz
    oveq2
    @66
    @23
    @10
    @26
    @14
    c.x
    @20
    cN
    @9
    cbc
    oveq1
    @66
    @25
    @12
    @13
    c.xp
    @66
    @24
    @11
    cA
    c.ex
    @20
    cN
    @9
    cmin
    oveq1
    oveq1d
    oveq1d
    oveq12d
    mpteq12dv
    oveq2d
    eqeq12d
    imbi2d
    @19
    c1
    cc0
    cA
    c.ex
    co
    #
    cc0
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cG
    c0g
    cfv
    #
    @39
    @31
    @19
    @70
    c1
    @71
    @71
    c.xp
    co
    #
    c.x
    co
    #
    @71
    @19
    @69
    @72
    c1
    c.x
    @19
    @67
    @71
    @68
    @71
    c.xp
    @19
    cA
    cG
    cbs
    cfv
    #
    wcel
    @67
    @71
    wceq
    @19
    cA
    cS
    @74
    @0
    @2
    @3
    @4
    simpr1
    #
    cS
    cR
    cG
    srgbinom.g
    srgbinom.s
    mgpbas
    #
    syl6eleq
    @74
    c.ex
    cG
    cA
    @71
    @74
    eqid
    #
    @71
    eqid
    #
    srgbinom.e
    mulg0
    syl
    @19
    cB
    @74
    wcel
    @68
    @71
    wceq
    @19
    cB
    cS
    @74
    @0
    @2
    @3
    @4
    simpr2
    #
    @76
    syl6eleq
    @74
    c.ex
    cG
    cB
    @71
    @77
    @78
    srgbinom.e
    mulg0
    syl
    oveq12d
    oveq2d
    @19
    c1
    cR
    cur
    cfv
    #
    @80
    c.xp
    co
    #
    c.x
    co
    #
    @80
    wceq
    #
    @73
    @71
    wceq
    #
    @19
    @82
    c1
    @80
    c.x
    co
    #
    @80
    @19
    @81
    @80
    c1
    c.x
    @19
    @0
    @80
    cS
    wcel
    #
    wa
    #
    @81
    @80
    wceq
    @0
    @87
    @5
    @0
    @86
    cS
    cR
    @80
    srgbinom.s
    @80
    eqid
    #
    srgidcl
    #
    ancli
    adantr
    cS
    cR
    c.xp
    @80
    @80
    srgbinom.s
    srgbinom.m
    @88
    srglidm
    syl
    oveq2d
    @0
    @85
    @80
    wceq
    #
    @5
    @0
    @80
    cR
    cbs
    cfv
    #
    wcel
    @90
    @91
    cR
    @80
    @91
    eqid
    #
    @88
    srgidcl
    @91
    c.x
    cR
    @80
    @92
    srgbinom.t
    mulg1
    syl
    adantr
    eqtrd
    @80
    @71
    wceq
    #
    @83
    @84
    wb
    cR
    @80
    cG
    srgbinom.g
    @88
    ringidval
    #
    @93
    @82
    @73
    @80
    @71
    @93
    @81
    @72
    c1
    c.x
    @93
    @80
    @71
    @80
    @71
    c.xp
    @93
    id
    #
    @95
    oveq12d
    oveq2d
    @95
    eqeq12d
    ax-mp
    sylib
    eqtrd
    #
    @19
    @39
    cR
    vk
    cc0
    csn
    #
    @37
    cmpt
    #
    cgsu
    co
    #
    @70
    @19
    @38
    @98
    cR
    cgsu
    @19
    vk
    @32
    @97
    @37
    @32
    @97
    wceq
    #
    @19
    cc0
    cz
    wcel
    @100
    0z
    cc0
    fzsn
    ax-mp
    a1i
    mpteq1d
    oveq2d
    @19
    cR
    cmnd
    wcel
    #
    cc0
    cvv
    wcel
    #
    @70
    cS
    wcel
    @99
    @70
    wceq
    @0
    @101
    @5
    cR
    srgmnd
    adantr
    #
    @102
    @19
    c0ex
    a1i
    @19
    @70
    @71
    cS
    @96
    @0
    @71
    cS
    wcel
    @5
    @0
    @71
    @80
    cS
    @94
    @89
    syl5eqelr
    adantr
    eqeltrd
    @37
    cS
    @70
    vk
    cR
    cc0
    cvv
    srgbinom.s
    @9
    cc0
    wceq
    #
    @33
    c1
    @36
    @69
    c.x
    @104
    @33
    cc0
    cc0
    cbc
    co
    #
    c1
    @9
    cc0
    cc0
    cbc
    oveq2
    cc0
    cn0
    wcel
    @105
    c1
    wceq
    0nn0
    cc0
    bcn0
    ax-mp
    syl6eq
    @104
    @35
    @67
    @13
    @68
    c.xp
    @104
    @34
    cc0
    cA
    c.ex
    @104
    @34
    cc0
    cc0
    cmin
    co
    cc0
    @9
    cc0
    cc0
    cmin
    oveq2
    0m0e0
    syl6eq
    oveq1d
    @9
    cc0
    cB
    c.ex
    oveq1
    oveq12d
    oveq12d
    gsumsn
    syl3anc
    eqtrd
    @19
    @6
    @74
    wcel
    @31
    @71
    wceq
    @19
    @6
    cS
    @74
    @19
    @101
    @2
    @3
    @6
    cS
    wcel
    @103
    @75
    @79
    cS
    c.pl
    cR
    cA
    cB
    srgbinom.s
    srgbinom.a
    mndcl
    syl3anc
    @76
    syl6eleq
    @74
    c.ex
    cG
    @6
    @71
    @77
    @78
    srgbinom.e
    mulg0
    syl
    3eqtr4rd
    @41
    cn0
    wcel
    #
    @19
    @51
    @62
    @106
    @19
    @51
    @62
    @106
    @19
    wa
    @51
    cA
    cB
    c.pl
    cR
    cS
    c.x
    c.xp
    vk
    c.ex
    cG
    @41
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    @106
    @0
    @5
    simprl
    @19
    @2
    @106
    @75
    adantl
    @19
    @3
    @106
    @79
    adantl
    @2
    @3
    @4
    @0
    @106
    simprr3
    @106
    @19
    simpl
    @51
    id
    srgbinomlem
    exp31
    a2d
    nn0ind
    expd
    impcom
    imp
end
