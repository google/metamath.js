include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv1.mm"
include "cfv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cmadu.mm"
include "cpm2mp.mm"
include "cpl1.mm"
include "cn0.mm"
include "cv.mm"
include "cmgp.mm"
include "cmg.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "cco1.mm"
include "wral.mm"
include "ccpmat.mm"
include "eqid.mm"
include "cpmadumatpoly.mm"
include "wa.mm"
include "wi.mm"
include "cascl.mm"
include "cpmidpmat.mm"
include "cchpmat.mm"
include "cpmadurid.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "chcoeffeqlem.mm"
include "sylbid.mm"
include "exp31.mm"
include "com24.mm"
include "syl5.mm"
include "ex.mm"
include "mp2d.mm"
include "impl.mm"
include "reximdva.mm"
include "mpd.mm"

theorem chcoeffeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
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
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) A. n e. NN0 ( U ` ( G ` n ) ) = ( ( ( coe1 ` K ) ` n ) .* .1. ) )

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
    cR
    cv1
    cfv
    #
    cY
    cur
    cfv
    #
    cY
    cvsca
    cfv
    #
    co
    cM
    cT
    cfv
    c.mi
    co
    #
    @4
    cN
    cP
    cmadu
    co
    #
    cfv
    c.xp
    co
    #
    cN
    cR
    cpm2mp
    co
    #
    cfv
    #
    cA
    cpl1
    cfv
    #
    vn
    cn0
    vn
    cv
    #
    cG
    cfv
    cU
    cfv
    #
    @10
    cA
    cv1
    cfv
    #
    @9
    cmgp
    cfv
    cmg
    cfv
    #
    co
    #
    @9
    cvsca
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    wceq
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
    @11
    @10
    cK
    cco1
    cfv
    cfv
    c.1
    c.as
    co
    #
    wceq
    vn
    cn0
    wral
    #
    vb
    @19
    wrex
    #
    vs
    cn
    wrex
    cA
    cB
    @4
    cP
    @9
    cR
    cN
    cR
    ccpmat
    co
    #
    cT
    @3
    c.xp
    cU
    @2
    vn
    @13
    cG
    @7
    @15
    @5
    cM
    c.mi
    cN
    cW
    @12
    cY
    c.0
    @1
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.t
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.g
    @24
    eqid
    @3
    eqid
    #
    @2
    eqid
    #
    @1
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    chcoeffeq.w
    @9
    eqid
    #
    @12
    eqid
    #
    @15
    eqid
    #
    @13
    eqid
    #
    chcoeffeq.u
    @7
    eqid
    #
    cpmadumatpoly
    @0
    @20
    @23
    vs
    cn
    @0
    @18
    cn
    wcel
    #
    wa
    @17
    @22
    vb
    @19
    @0
    @35
    vb
    cv
    @19
    wcel
    #
    @17
    @22
    wi
    #
    @0
    cK
    @2
    @3
    co
    #
    @7
    cfv
    #
    @9
    vn
    cn0
    @21
    @14
    @15
    co
    cmpt
    cgsu
    co
    #
    wceq
    #
    @6
    @38
    wceq
    #
    @35
    @36
    wa
    #
    @37
    wi
    cA
    cB
    cC
    cP
    @9
    cR
    @15
    cT
    @3
    cP
    cascl
    cfv
    #
    @2
    vn
    @13
    cP
    cmgp
    cfv
    cmg
    cfv
    #
    @38
    @7
    c.as
    cK
    cM
    cN
    c.1
    cW
    @1
    cY
    @12
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    @27
    @45
    eqid
    @25
    @26
    @44
    eqid
    chcoeffeq.c
    chcoeffeq.k
    @38
    eqid
    chcoeffeq.1
    chcoeffeq.m
    chcoeffeq.t
    chcoeffeq.w
    @30
    @31
    @32
    @33
    @34
    cpmidpmat
    @0
    @6
    cM
    cN
    cR
    cchpmat
    co
    #
    cfv
    #
    @2
    @3
    co
    @38
    cA
    cB
    @46
    cP
    cR
    cT
    @3
    c.xp
    @2
    @4
    @5
    cM
    c.mi
    cN
    @1
    cY
    chcoeffeq.a
    chcoeffeq.b
    @46
    eqid
    chcoeffeq.p
    chcoeffeq.y
    @27
    chcoeffeq.t
    chcoeffeq.s
    @25
    @26
    @28
    @29
    chcoeffeq.r
    cpmadurid
    @0
    @47
    cK
    @2
    @3
    @0
    cK
    @47
    cK
    @47
    wceq
    @0
    cK
    cM
    cC
    cfv
    @47
    chcoeffeq.k
    cM
    cC
    @46
    chcoeffeq.c
    fveq1i
    eqtri
    a1i
    eqcomd
    oveq1d
    eqtrd
    @0
    @43
    @42
    @41
    @37
    @0
    @43
    @42
    @41
    @37
    wi
    #
    wi
    @42
    @8
    @39
    wceq
    #
    @0
    @43
    wa
    #
    @48
    @6
    @38
    @7
    fveq2
    @50
    @17
    @41
    @49
    @22
    @50
    @17
    @41
    @49
    @22
    wi
    @50
    @17
    wa
    #
    @41
    wa
    #
    @49
    @16
    @40
    wceq
    #
    @22
    @52
    @8
    @16
    @39
    @40
    @51
    @17
    @41
    @50
    @17
    simpr
    adantr
    @51
    @41
    simpr
    eqeq12d
    @51
    @53
    @22
    wi
    #
    @41
    @50
    @54
    @17
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
    chcoeffeqlem
    adantr
    adantr
    sylbid
    exp31
    com24
    syl5
    ex
    com24
    mp2d
    impl
    reximdva
    reximdva
    mpd
end
