include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
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
include "cplusg.mm"
include "eqid.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "eqeq1.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "cpmadugsum.mm"
include "wa.mm"
include "crg.mm"
include "simp1.mm"
include "ad3antrrr.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "wf.mm"
include "chfacfisfcpmat.mm"
include "syl3anl2.mm"
include "anassrs.mm"
include "ffvelrnda.mm"
include "m2cpminvid2.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "eqeq2d.mm"
include "ccom.mm"
include "c0g.mm"
include "cfsupp.mm"
include "3simpa.mm"
include "ad2antrr.mm"
include "cpmadumatpolylem1.mm"
include "cpmadumatpolylem2.mm"
include "pm2mp.mm"
include "syl12anc.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "sylbid.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cpmadumatpoly
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let c.as: class .*
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  let vz: setvar z
  assume cpmadumatpoly.a: |- A = ( N Mat R )
  assume cpmadumatpoly.b: |- B = ( Base ` A )
  assume cpmadumatpoly.p: |- P = ( Poly1 ` R )
  assume cpmadumatpoly.y: |- Y = ( N Mat P )
  assume cpmadumatpoly.t: |- T = ( N matToPolyMat R )
  assume cpmadumatpoly.r: |- .X. = ( .r ` Y )
  assume cpmadumatpoly.m0: |- .- = ( -g ` Y )
  assume cpmadumatpoly.0: |- .0. = ( 0g ` Y )
  assume cpmadumatpoly.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cpmadumatpoly.s: |- S = ( N ConstPolyMat R )
  assume cpmadumatpoly.m1: |- .x. = ( .s ` Y )
  assume cpmadumatpoly.1: |- .1. = ( 1r ` Y )
  assume cpmadumatpoly.z: |- Z = ( var1 ` R )
  assume cpmadumatpoly.d: |- D = ( ( Z .x. .1. ) .- ( T ` M ) )
  assume cpmadumatpoly.j: |- J = ( N maAdju P )
  assume cpmadumatpoly.w: |- W = ( Base ` Y )
  assume cpmadumatpoly.q: |- Q = ( Poly1 ` A )
  assume cpmadumatpoly.x: |- X = ( var1 ` A )
  assume cpmadumatpoly.m2: |- .* = ( .s ` Q )
  assume cpmadumatpoly.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume cpmadumatpoly.u: |- U = ( N cPolyMatToMat R )
  assume cpmadumatpoly.i: |- I = ( N pMatToMatPoly R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint S n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint A b
  disjoint A s
  disjoint b s
  disjoint A n
  disjoint B b
  disjoint B s
  disjoint D b
  disjoint D s
  disjoint D n
  disjoint G n
  disjoint I n
  disjoint J b
  disjoint J s
  disjoint J n
  disjoint M b
  disjoint M s
  disjoint N b
  disjoint N s
  disjoint P n
  disjoint P b
  disjoint P s
  disjoint R b
  disjoint R s
  disjoint T b
  disjoint T s
  disjoint T n
  disjoint U n
  disjoint W n
  disjoint Y b
  disjoint Y s
  disjoint Z b
  disjoint Z s
  disjoint Z n
  disjoint .X. n
  disjoint .x. b
  disjoint .x. s
  disjoint .x. n
  disjoint .1. n
  disjoint .0. n
  disjoint .- n
  disjoint A z
  disjoint b z
  disjoint s z
  disjoint B z
  disjoint D z
  disjoint J z
  disjoint M z
  disjoint N z
  disjoint P z
  disjoint R z
  disjoint T z
  disjoint Y z
  disjoint Z z
  disjoint .X. z
  disjoint n z
  disjoint .x. z
  disjoint .0. z
  disjoint .- z
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( I ` ( D .X. ( J ` D ) ) ) = ( Q gsum ( n e. NN0 |-> ( ( U ` ( G ` n ) ) .* ( n .^ X ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cD
    cD
    cJ
    cfv
    c.xp
    co
    #
    cY
    vn
    cn0
    vn
    cv
    #
    cZ
    cP
    cmgp
    cfv
    cmg
    cfv
    #
    co
    #
    @5
    cG
    cfv
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
    @4
    cI
    cfv
    #
    cQ
    vn
    cn0
    @8
    cU
    cfv
    #
    @5
    cX
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
    #
    wceq
    #
    vb
    @14
    wrex
    #
    vs
    cn
    wrex
    cA
    cB
    cP
    cY
    cplusg
    cfv
    #
    cR
    cT
    c.x
    c.xp
    c.1
    vn
    vz
    @6
    cG
    cD
    cJ
    cM
    c.mi
    cN
    cZ
    cY
    c.0
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.t
    cpmadumatpoly.z
    @6
    eqid
    #
    cpmadumatpoly.m1
    cpmadumatpoly.r
    cpmadumatpoly.1
    @24
    eqid
    cpmadumatpoly.m0
    cpmadumatpoly.d
    cpmadumatpoly.j
    cpmadumatpoly.0
    cG
    vn
    cn0
    @5
    cc0
    wceq
    #
    c.0
    cM
    cT
    cfv
    #
    cc0
    vb
    cv
    #
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    #
    @5
    @13
    c1
    caddc
    co
    #
    wceq
    #
    @13
    @28
    cfv
    cT
    cfv
    #
    @30
    @5
    clt
    wbr
    #
    c.0
    @5
    c1
    cmin
    co
    #
    @28
    cfv
    #
    cT
    cfv
    #
    @27
    @5
    @28
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cmpt
    vz
    cn0
    vz
    cv
    #
    cc0
    wceq
    #
    @29
    @44
    @30
    wceq
    #
    @32
    @30
    @44
    clt
    wbr
    #
    c.0
    @44
    c1
    cmin
    co
    #
    @28
    cfv
    #
    cT
    cfv
    #
    @27
    @44
    @28
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cmpt
    cpmadumatpoly.g
    vn
    vz
    cn0
    @43
    @57
    @5
    @44
    wceq
    #
    @26
    @45
    @42
    @56
    @29
    @5
    @44
    cc0
    eqeq1
    @58
    @31
    @46
    @41
    @55
    @32
    @5
    @44
    @30
    eqeq1
    @58
    @33
    @47
    @40
    @54
    c.0
    @5
    @44
    @30
    clt
    breq2
    @58
    @36
    @50
    @39
    @53
    c.mi
    @58
    @35
    @49
    cT
    @58
    @34
    @48
    @28
    @5
    @44
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    @58
    @38
    @52
    @27
    c.xp
    @58
    @37
    @51
    cT
    @5
    @44
    @28
    fveq2
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    ifbieq2d
    ifbieq2d
    cbvmptv
    eqtri
    cpmadugsum
    @3
    @15
    @23
    vs
    cn
    @3
    @13
    cn
    wcel
    #
    wa
    #
    @12
    @22
    vb
    @14
    @60
    @28
    @14
    wcel
    #
    wa
    #
    @12
    @4
    cY
    vn
    cn0
    @7
    @17
    cT
    cfv
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
    @22
    @62
    @11
    @66
    @4
    @62
    @10
    @65
    cY
    cgsu
    @62
    vn
    cn0
    @9
    @64
    @62
    @5
    cn0
    wcel
    #
    wa
    #
    @8
    @63
    @7
    c.x
    @69
    @63
    @8
    @69
    @0
    cR
    crg
    wcel
    #
    @8
    cS
    wcel
    @63
    @8
    wceq
    @3
    @0
    @59
    @61
    @68
    @0
    @1
    @2
    simp1
    ad3antrrr
    @3
    @70
    @59
    @61
    @68
    @1
    @0
    @70
    @2
    cR
    crngring
    #
    3ad2ant2
    ad3antrrr
    @62
    cn0
    cS
    @5
    cG
    @3
    @59
    @61
    cn0
    cS
    cG
    wf
    #
    @1
    @0
    @70
    @2
    @59
    @61
    wa
    @72
    @71
    cA
    cB
    cP
    cR
    cS
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.r
    cpmadumatpoly.m0
    cpmadumatpoly.0
    cpmadumatpoly.t
    cpmadumatpoly.g
    cpmadumatpoly.s
    chfacfisfcpmat
    syl3anl2
    anassrs
    #
    ffvelrnda
    cR
    cS
    cT
    cU
    @8
    cN
    cpmadumatpoly.s
    cpmadumatpoly.u
    cpmadumatpoly.t
    m2cpminvid2
    syl3anc
    eqcomd
    oveq2d
    mpteq2dva
    oveq2d
    eqeq2d
    @62
    @67
    @22
    @67
    @62
    @16
    @66
    cI
    cfv
    #
    @21
    @4
    @66
    cI
    fveq2
    @62
    cY
    vn
    cn0
    @7
    @5
    cU
    cG
    ccom
    #
    cfv
    #
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cI
    cfv
    #
    cQ
    vn
    cn0
    @76
    @18
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @74
    @21
    @62
    @0
    @1
    wa
    #
    @75
    cB
    cn0
    cmap
    co
    wcel
    @75
    cA
    c0g
    cfv
    cfsupp
    wbr
    @81
    @84
    wceq
    @3
    @85
    @59
    @61
    @0
    @1
    @2
    3simpa
    ad2antrr
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    cT
    c.x
    c.xp
    cU
    c.1
    vn
    c.ex
    cG
    c.as
    cJ
    cM
    c.mi
    cN
    cW
    cX
    cY
    c.0
    cZ
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.t
    cpmadumatpoly.r
    cpmadumatpoly.m0
    cpmadumatpoly.0
    cpmadumatpoly.g
    cpmadumatpoly.s
    cpmadumatpoly.m1
    cpmadumatpoly.1
    cpmadumatpoly.z
    cpmadumatpoly.d
    cpmadumatpoly.j
    cpmadumatpoly.w
    cpmadumatpoly.q
    cpmadumatpoly.x
    cpmadumatpoly.m2
    cpmadumatpoly.e
    cpmadumatpoly.u
    cpmadumatpolylem1
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    cT
    c.x
    c.xp
    cU
    c.1
    vn
    c.ex
    cG
    c.as
    cJ
    cM
    c.mi
    cN
    cW
    cX
    cY
    c.0
    cZ
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.t
    cpmadumatpoly.r
    cpmadumatpoly.m0
    cpmadumatpoly.0
    cpmadumatpoly.g
    cpmadumatpoly.s
    cpmadumatpoly.m1
    cpmadumatpoly.1
    cpmadumatpoly.z
    cpmadumatpoly.d
    cpmadumatpoly.j
    cpmadumatpoly.w
    cpmadumatpoly.q
    cpmadumatpoly.x
    cpmadumatpoly.m2
    cpmadumatpoly.e
    cpmadumatpoly.u
    cpmadumatpolylem2
    cA
    cW
    cY
    cP
    cQ
    cR
    cT
    c.x
    vn
    @6
    c.ex
    cI
    c.as
    cB
    @75
    cN
    cX
    cZ
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.w
    cpmadumatpoly.m2
    cpmadumatpoly.e
    cpmadumatpoly.x
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.q
    cpmadumatpoly.i
    @25
    cpmadumatpoly.z
    cpmadumatpoly.m1
    cpmadumatpoly.t
    pm2mp
    syl12anc
    @62
    @66
    @80
    cI
    @62
    @65
    @79
    cY
    cgsu
    @62
    vn
    cn0
    @64
    @78
    @69
    @63
    @77
    @7
    c.x
    @69
    @17
    @76
    cT
    @62
    @72
    @68
    @17
    @76
    wceq
    @73
    @72
    @68
    wa
    @76
    @17
    cn0
    cS
    @5
    cU
    cG
    fvco3
    eqcomd
    sylan
    #
    fveq2d
    oveq2d
    mpteq2dva
    oveq2d
    fveq2d
    @62
    @20
    @83
    cQ
    cgsu
    @62
    vn
    cn0
    @19
    @82
    @69
    @17
    @76
    @18
    c.as
    @86
    oveq1d
    mpteq2dva
    oveq2d
    3eqtr4d
    sylan9eqr
    ex
    sylbid
    reximdva
    reximdva
    mpd
end
