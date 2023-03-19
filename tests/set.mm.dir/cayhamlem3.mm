include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cco1.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wral.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "chcoeffeq.mm"
include "wa.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "wi.mm"
include "rspccva.mm"
include "cbs.mm"
include "simprll.mm"
include "wf.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "syl.mm"
include "syl5eqel.mm"
include "coe1f.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "nn0ex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "simpl.mm"
include "cayhamlem2.mm"
include "syl12anc.mm"
include "adantl.mm"
include "oveq2.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "exp32.mm"
include "com12.mm"
include "mpd.mm"
include "impl.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "ex.mm"
include "syl5bi.mm"
include "reximdva.mm"

theorem cayhamlem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let c.as: class .*
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vl: setvar l
  assume chcoeffeq.a: |- A = ( N Mat R )
  assume chcoeffeq.b: |- B = ( Base ` A )
  assume chcoeffeq.p: |- P = ( Poly1 ` R )
  assume chcoeffeq.y: |- Y = ( N Mat P )
  assume chcoeffeq.r: |- .X. = ( .r ` Y )
  assume chcoeffeq.s: |- .- = ( -g ` Y )
  assume chcoeffeq.0: |- .0. = ( 0g ` Y )
  assume chcoeffeq.t: |- T = ( N matToPolyMat R )
  assume chcoeffeq.c: |- C = ( N CharPlyMat R )
  assume chcoeffeq.k: |- K = ( C ` M )
  assume chcoeffeq.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chcoeffeq.w: |- W = ( Base ` Y )
  assume chcoeffeq.1: |- .1. = ( 1r ` A )
  assume chcoeffeq.m: |- .* = ( .s ` A )
  assume chcoeffeq.u: |- U = ( N cPolyMatToMat R )
  assume cayhamlem.e1: |- .^ = ( .g ` ( mulGrp ` A ) )
  assume cayhamlem.r: |- .x. = ( .r ` A )

  disjoint A n
  disjoint B n
  disjoint G n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint U n
  disjoint Y n
  disjoint .1. n
  disjoint .* n
  disjoint b n
  disjoint n s
  disjoint A b
  disjoint A s
  disjoint b s
  disjoint B b
  disjoint B s
  disjoint M b
  disjoint M s
  disjoint N b
  disjoint N s
  disjoint P b
  disjoint P n
  disjoint P s
  disjoint R b
  disjoint R s
  disjoint T b
  disjoint T n
  disjoint T s
  disjoint W n
  disjoint Y b
  disjoint Y s
  disjoint .0. n
  disjoint .X. n
  disjoint .- b
  disjoint .- n
  disjoint .- s
  disjoint A l
  disjoint l n
  disjoint B l
  disjoint G l
  disjoint K l
  disjoint M l
  disjoint N l
  disjoint R l
  disjoint U l
  disjoint .1. l
  disjoint .* l
  disjoint b l
  disjoint l s
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( A gsum ( n e. NN0 |-> ( ( ( coe1 ` K ) ` n ) .* ( n .^ M ) ) ) ) = ( A gsum ( n e. NN0 |-> ( ( n .^ M ) .x. ( U ` ( G ` n ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    cR
    ccrg
    wcel
    cM
    cB
    wcel
    w3a
    #
    vn
    cv
    #
    cG
    cfv
    #
    cU
    cfv
    #
    @1
    cK
    cco1
    cfv
    #
    cfv
    #
    c.1
    c.as
    co
    #
    wceq
    #
    vn
    cn0
    wral
    #
    vb
    cB
    cc0
    vs
    cv
    #
    cfz
    co
    cmap
    co
    #
    wrex
    #
    vs
    cn
    wrex
    cA
    vn
    cn0
    @5
    @1
    cM
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    cA
    vn
    cn0
    @12
    @3
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    wceq
    #
    vb
    @10
    wrex
    #
    vs
    cn
    wrex
    cA
    cB
    cC
    cP
    cR
    cT
    c.xp
    cU
    c.1
    vn
    cG
    c.as
    cK
    cM
    c.mi
    cN
    cW
    cY
    c.0
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.t
    chcoeffeq.c
    chcoeffeq.k
    chcoeffeq.g
    chcoeffeq.w
    chcoeffeq.1
    chcoeffeq.m
    chcoeffeq.u
    chcoeffeq
    @0
    @11
    @18
    vs
    cn
    @0
    @9
    cn
    wcel
    #
    wa
    #
    @8
    @17
    vb
    @10
    @8
    vl
    cv
    #
    cG
    cfv
    #
    cU
    cfv
    #
    @21
    @4
    cfv
    #
    c.1
    c.as
    co
    #
    wceq
    #
    vl
    cn0
    wral
    #
    @20
    vb
    cv
    @10
    wcel
    #
    wa
    #
    @17
    @7
    @26
    vn
    vl
    cn0
    @1
    @21
    wceq
    #
    @3
    @23
    @6
    @25
    @30
    @2
    @22
    cU
    @1
    @21
    cG
    fveq2
    fveq2d
    @30
    @5
    @24
    c.1
    c.as
    @1
    @21
    @4
    fveq2
    oveq1d
    eqeq12d
    cbvralv
    @29
    @27
    @17
    @29
    @27
    wa
    #
    @14
    @16
    cA
    cgsu
    @31
    vn
    cn0
    @13
    @15
    @29
    @27
    @1
    cn0
    wcel
    #
    @13
    @15
    wceq
    #
    @27
    @32
    wa
    #
    @29
    @33
    @34
    @7
    @29
    @33
    wi
    #
    @26
    @7
    vl
    @1
    cn0
    @21
    @1
    wceq
    #
    @23
    @3
    @25
    @6
    @36
    @22
    @2
    cU
    @21
    @1
    cG
    fveq2
    fveq2d
    @36
    @24
    @5
    c.1
    c.as
    @21
    @1
    @4
    fveq2
    oveq1d
    eqeq12d
    rspccva
    @32
    @7
    @35
    wi
    @27
    @7
    @32
    @35
    @7
    @32
    @29
    @33
    @7
    @32
    @29
    wa
    #
    wa
    @13
    @12
    @6
    c.x
    co
    #
    @15
    @37
    @13
    @38
    wceq
    #
    @7
    @37
    @0
    @4
    cR
    cbs
    cfv
    #
    cn0
    cmap
    co
    wcel
    #
    @32
    @39
    @32
    @0
    @19
    @28
    simprll
    #
    @37
    @41
    cn0
    @40
    @4
    wf
    #
    @37
    cK
    cP
    cbs
    cfv
    #
    wcel
    @43
    @37
    cK
    cM
    cC
    cfv
    #
    @44
    chcoeffeq.k
    @37
    @0
    @45
    @44
    wcel
    @42
    cA
    cB
    cC
    cP
    cR
    @44
    cM
    cN
    chcoeffeq.c
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    @44
    eqid
    #
    chpmatply1
    syl
    syl5eqel
    @4
    @44
    cP
    cR
    cK
    @40
    @4
    eqid
    @46
    chcoeffeq.p
    @40
    eqid
    #
    coe1f
    syl
    @40
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    wa
    @41
    @43
    wb
    @37
    @48
    @49
    cR
    cbs
    fvex
    nn0ex
    pm3.2i
    @40
    cn0
    @4
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @32
    @29
    simpl
    cA
    cB
    cR
    c.x
    c.1
    c.ex
    @4
    c.as
    @40
    @1
    cM
    cN
    @47
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.1
    chcoeffeq.m
    cayhamlem.e1
    cayhamlem.r
    cayhamlem2
    syl12anc
    adantl
    @7
    @15
    @38
    wceq
    @37
    @3
    @6
    @12
    c.x
    oveq2
    adantr
    eqtr4d
    exp32
    com12
    adantl
    mpd
    com12
    impl
    mpteq2dva
    oveq2d
    ex
    syl5bi
    reximdva
    reximdva
    mpd
end
