include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cco1.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "eqid.mm"
include "cayhamlem4.mm"
include "wa.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "cayhamlem1.mm"
include "syl5eq.mm"
include "c0g.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "m2cpminv0.mm"
include "syl.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem cayleyhamilton0
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
  let cE: class E
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
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  let vl: setvar l
  assume cayleyhamilton0.a: |- A = ( N Mat R )
  assume cayleyhamilton0.b: |- B = ( Base ` A )
  assume cayleyhamilton0.0: |- .0. = ( 0g ` A )
  assume cayleyhamilton0.1: |- .1. = ( 1r ` A )
  assume cayleyhamilton0.m: |- .* = ( .s ` A )
  assume cayleyhamilton0.e1: |- .^ = ( .g ` ( mulGrp ` A ) )
  assume cayleyhamilton0.c: |- C = ( N CharPlyMat R )
  assume cayleyhamilton0.k: |- K = ( coe1 ` ( C ` M ) )
  assume cayleyhamilton0.p: |- P = ( Poly1 ` R )
  assume cayleyhamilton0.y: |- Y = ( N Mat P )
  assume cayleyhamilton0.r: |- .X. = ( .r ` Y )
  assume cayleyhamilton0.s: |- .- = ( -g ` Y )
  assume cayleyhamilton0.z: |- Z = ( 0g ` Y )
  assume cayleyhamilton0.w: |- W = ( Base ` Y )
  assume cayleyhamilton0.e2: |- E = ( .g ` ( mulGrp ` Y ) )
  assume cayleyhamilton0.t: |- T = ( N matToPolyMat R )
  assume cayleyhamilton0.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( Z .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , Z , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cayleyhamilton0.u: |- U = ( N cPolyMatToMat R )

  disjoint A b
  disjoint A n
  disjoint A s
  disjoint b n
  disjoint b s
  disjoint n s
  disjoint B b
  disjoint B n
  disjoint B s
  disjoint C n
  disjoint E n
  disjoint G n
  disjoint K b
  disjoint K s
  disjoint M b
  disjoint M n
  disjoint M s
  disjoint N b
  disjoint N n
  disjoint N s
  disjoint P b
  disjoint P n
  disjoint P s
  disjoint R b
  disjoint R n
  disjoint R s
  disjoint T b
  disjoint T n
  disjoint T s
  disjoint U n
  disjoint W n
  disjoint Y b
  disjoint Y n
  disjoint Y s
  disjoint Z n
  disjoint .* b
  disjoint .* n
  disjoint .* s
  disjoint .- b
  disjoint .- n
  disjoint .- s
  disjoint .0. b
  disjoint .0. s
  disjoint .1. n
  disjoint .X. n
  disjoint .^ b
  disjoint .^ n
  disjoint .^ s
  disjoint B l
  disjoint b l
  disjoint l n
  disjoint l s
  disjoint E l
  disjoint G l
  disjoint M l
  disjoint N l
  disjoint R l
  disjoint T l
  disjoint Y l
  disjoint .- l
  disjoint .X. l
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( A gsum ( n e. NN0 |-> ( ( K ` n ) .* ( n .^ M ) ) ) ) = .0. )

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
    cA
    vn
    cn0
    vn
    cv
    #
    cM
    cC
    cfv
    #
    cco1
    cfv
    #
    cfv
    #
    @4
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
    #
    cY
    vn
    cn0
    @4
    cM
    cT
    cfv
    #
    cE
    co
    #
    @4
    cG
    cfv
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cU
    cfv
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
    vs
    cn
    wrex
    cA
    vn
    cn0
    @4
    cK
    cfv
    #
    @8
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    wceq
    #
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
    cE
    c.ex
    cG
    c.as
    @5
    cM
    c.mi
    cN
    cW
    cY
    cZ
    vs
    vb
    cayleyhamilton0.a
    cayleyhamilton0.b
    cayleyhamilton0.p
    cayleyhamilton0.y
    cayleyhamilton0.r
    cayleyhamilton0.s
    cayleyhamilton0.z
    cayleyhamilton0.t
    cayleyhamilton0.c
    @5
    eqid
    cayleyhamilton0.g
    cayleyhamilton0.w
    cayleyhamilton0.1
    cayleyhamilton0.m
    cayleyhamilton0.u
    cayleyhamilton0.e1
    cayleyhamilton0.e2
    cayhamlem4
    @3
    @19
    @26
    vs
    vb
    cn
    @21
    @3
    @20
    cn
    wcel
    vb
    cv
    @21
    wcel
    wa
    #
    wa
    #
    @19
    @26
    @28
    @19
    wa
    @25
    @18
    c.0
    @28
    @19
    @25
    @18
    wceq
    @28
    @11
    @25
    @18
    @28
    @10
    @24
    cA
    cgsu
    @28
    vn
    cn0
    @9
    @23
    @28
    @4
    cn0
    wcel
    wa
    #
    @7
    @22
    @8
    c.as
    @29
    @4
    @6
    cK
    @6
    cK
    wceq
    @29
    cK
    @6
    cayleyhamilton0.k
    eqcomi
    a1i
    fveq1d
    oveq1d
    mpteq2dva
    oveq2d
    eqeq1d
    biimpa
    @28
    @18
    c.0
    wceq
    #
    @19
    @28
    @17
    cZ
    wceq
    #
    @30
    @28
    @17
    cY
    vl
    cn0
    vl
    cv
    #
    @12
    cE
    co
    #
    @32
    cG
    cfv
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    cZ
    @16
    @36
    cY
    cgsu
    vn
    vl
    cn0
    @15
    @35
    @4
    @32
    wceq
    @13
    @33
    @14
    @34
    c.xp
    @4
    @32
    @12
    cE
    oveq1
    @4
    @32
    cG
    fveq2
    oveq12d
    cbvmptv
    oveq2i
    cA
    cB
    cP
    cR
    cT
    c.xp
    vl
    vn
    cE
    cG
    cM
    c.mi
    cN
    cY
    cZ
    vs
    vb
    cayleyhamilton0.a
    cayleyhamilton0.b
    cayleyhamilton0.p
    cayleyhamilton0.y
    cayleyhamilton0.r
    cayleyhamilton0.s
    cayleyhamilton0.z
    cayleyhamilton0.t
    cayleyhamilton0.g
    cayleyhamilton0.e2
    cayhamlem1
    syl5eq
    @31
    @28
    @18
    cZ
    cU
    cfv
    #
    c.0
    @17
    cZ
    cU
    fveq2
    @3
    @37
    c.0
    wceq
    @27
    @3
    @37
    cA
    c0g
    cfv
    #
    c.0
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @37
    @38
    wceq
    @0
    @1
    @40
    @2
    @1
    @39
    @0
    cR
    crngring
    anim2i
    3adant3
    cA
    cY
    cP
    cR
    cU
    cN
    @38
    cZ
    cayleyhamilton0.a
    cayleyhamilton0.u
    cayleyhamilton0.p
    cayleyhamilton0.y
    @38
    eqid
    cayleyhamilton0.z
    m2cpminv0
    syl
    cayleyhamilton0.0
    syl6eqr
    adantr
    sylan9eqr
    mpdan
    adantr
    eqtrd
    ex
    rexlimdvva
    mpd
end
