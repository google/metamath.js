include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "cres.mm"
include "climc.mm"
include "cc.mm"
include "ccncf.mm"
include "wceq.mm"
include "csb.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "c2.mm"
include "csin.mm"
include "cmul.mm"
include "wss.mm"
include "cr.mm"
include "adantr.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "cicc.mm"
include "cpi.mm"
include "cneg.mm"
include "simpr.mm"
include "biid.mm"
include "fourierdlem50.mm"
include "simpld.mm"
include "id.mm"
include "simprd.mm"
include "jca31.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfif.mm"
include "nfov.mm"
include "nfel1.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "sseq2d.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "eqid.mm"
include "fourierdlem76.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "syl5eqel.mm"

theorem fourierdlem86
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vp: setvar p
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem86.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem86.xre: |- ( ph -> X e. RR )
  assume fourierdlem86.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( -u _pi + X ) /\ ( p ` m ) = ( _pi + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem86.m: |- ( ph -> M e. NN )
  assume fourierdlem86.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem86.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) e. ( ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem86.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` i ) ) )
  assume fourierdlem86.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` ( i + 1 ) ) ) )
  assume fourierdlem86.a: |- ( ph -> A e. RR )
  assume fourierdlem86.b: |- ( ph -> B e. RR )
  assume fourierdlem86.altb: |- ( ph -> A < B )
  assume fourierdlem86.ab: |- ( ph -> ( A [,] B ) C_ ( -u _pi [,] _pi ) )
  assume fourierdlem86.n0: |- ( ph -> -. 0 e. ( A [,] B ) )
  assume fourierdlem86.c: |- ( ph -> C e. RR )
  assume fourierdlem86.o: |- O = ( s e. ( A [,] B ) |-> ( ( ( ( F ` ( X + s ) ) - C ) / s ) x. ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem86.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )
  assume fourierdlem86.t: |- T = ( { A , B } u. ( ran Q i^i ( A (,) B ) ) )
  assume fourierdlem86.n: |- N = ( ( # ` T ) - 1 )
  assume fourierdlem86.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , T ) )
  assume fourierdlem86.d: |- D = ( ( ( if ( ( S ` ( j + 1 ) ) = ( Q ` ( U + 1 ) ) , [_ U / i ]_ L , ( F ` ( X + ( S ` ( j + 1 ) ) ) ) ) - C ) / ( S ` ( j + 1 ) ) ) x. ( ( S ` ( j + 1 ) ) / ( 2 x. ( sin ` ( ( S ` ( j + 1 ) ) / 2 ) ) ) ) )
  assume fourierdlem86.e: |- E = ( ( ( if ( ( S ` j ) = ( Q ` U ) , [_ U / i ]_ R , ( F ` ( X + ( S ` j ) ) ) ) - C ) / ( S ` j ) ) x. ( ( S ` j ) / ( 2 x. ( sin ` ( ( S ` j ) / 2 ) ) ) ) )
  assume fourierdlem86.u: |- U = ( iota_ i e. ( 0 ..^ M ) ( ( S ` j ) (,) ( S ` ( j + 1 ) ) ) C_ ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) )

  disjoint A s
  disjoint B s
  disjoint C i
  disjoint C s
  disjoint i s
  disjoint F i
  disjoint F s
  disjoint L s
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint M j
  disjoint M s
  disjoint i j
  disjoint j s
  disjoint N f
  disjoint N i
  disjoint N s
  disjoint O i
  disjoint Q i
  disjoint Q s
  disjoint R s
  disjoint S f
  disjoint S i
  disjoint S s
  disjoint T f
  disjoint U i
  disjoint V i
  disjoint V p
  disjoint V j
  disjoint V s
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X j
  disjoint X s
  disjoint f j
  disjoint f ph
  disjoint j ph
  disjoint i ph
  disjoint ph s
  disjoint M y
  disjoint i y
  disjoint j y
  disjoint N y
  disjoint Q y
  disjoint S y
  disjoint V y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ( ph /\ j e. ( 0 ..^ N ) ) -> ( ( D e. ( ( O |` ( ( S ` j ) (,) ( S ` ( j + 1 ) ) ) ) limCC ( S ` ( j + 1 ) ) ) /\ E e. ( ( O |` ( ( S ` j ) (,) ( S ` ( j + 1 ) ) ) ) limCC ( S ` j ) ) ) /\ ( O |` ( ( S ` j ) (,) ( S ` ( j + 1 ) ) ) ) e. ( ( ( S ` j ) (,) ( S ` ( j + 1 ) ) ) -cn-> CC ) ) )

  proof
    wph
    vj
    cv
    #
    cc0
    cN
    cfzo
    co
    wcel
    #
    wa
    #
    cD
    cO
    @0
    cS
    cfv
    #
    @0
    c1
    caddc
    co
    cS
    cfv
    #
    cioo
    co
    #
    cres
    #
    @4
    climc
    co
    #
    wcel
    cE
    @6
    @3
    climc
    co
    #
    wcel
    @6
    @5
    cc
    ccncf
    co
    wcel
    #
    @2
    cD
    @4
    cU
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    vi
    cU
    cL
    csb
    #
    cX
    @4
    caddc
    co
    cF
    cfv
    #
    cif
    #
    cC
    cmin
    co
    #
    @4
    cdiv
    co
    #
    @4
    c2
    @4
    c2
    cdiv
    co
    csin
    cfv
    cmul
    co
    cdiv
    co
    #
    cmul
    co
    #
    @7
    fourierdlem86.d
    @2
    @19
    @7
    wcel
    #
    @3
    cU
    cQ
    cfv
    #
    wceq
    #
    vi
    cU
    cR
    csb
    #
    cX
    @3
    caddc
    co
    cF
    cfv
    #
    cif
    #
    cC
    cmin
    co
    #
    @3
    cdiv
    co
    #
    @3
    c2
    @3
    c2
    cdiv
    co
    csin
    cfv
    cmul
    co
    cdiv
    co
    #
    cmul
    co
    #
    @8
    wcel
    #
    @2
    @20
    @30
    wa
    #
    @9
    @2
    cU
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @2
    @33
    wa
    #
    @5
    @21
    @11
    cioo
    co
    #
    wss
    #
    wa
    #
    @31
    @9
    wa
    #
    @2
    @33
    @36
    @2
    @2
    vi
    cv
    #
    @32
    wcel
    #
    wa
    #
    @5
    @39
    cQ
    cfv
    #
    @39
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wss
    #
    wa
    #
    vy
    cv
    #
    @32
    wcel
    wa
    @5
    @48
    cQ
    cfv
    @48
    c1
    caddc
    co
    cQ
    cfv
    cioo
    co
    wss
    wa
    #
    cA
    cB
    cP
    cQ
    cS
    cT
    cU
    vf
    vi
    vy
    vm
    @0
    cM
    cN
    cV
    cX
    vp
    wph
    cX
    cr
    wcel
    @1
    fourierdlem86.xre
    adantr
    fourierdlem86.p
    wph
    cM
    cn
    wcel
    @1
    fourierdlem86.m
    adantr
    wph
    cV
    cM
    cP
    cfv
    wcel
    @1
    fourierdlem86.v
    adantr
    wph
    cA
    cr
    wcel
    @1
    fourierdlem86.a
    adantr
    wph
    cB
    cr
    wcel
    @1
    fourierdlem86.b
    adantr
    wph
    cA
    cB
    clt
    wbr
    @1
    fourierdlem86.altb
    adantr
    wph
    cA
    cB
    cicc
    co
    cpi
    cneg
    cpi
    cicc
    co
    wss
    @1
    fourierdlem86.ab
    adantr
    fourierdlem86.q
    fourierdlem86.t
    fourierdlem86.n
    fourierdlem86.s
    wph
    @1
    simpr
    fourierdlem86.u
    @49
    biid
    fourierdlem50
    #
    simpld
    #
    @2
    @2
    @33
    @36
    @2
    id
    @51
    @2
    @33
    @36
    @50
    simprd
    jca31
    @47
    @4
    @44
    wceq
    #
    cL
    @14
    cif
    #
    cC
    cmin
    co
    #
    @4
    cdiv
    co
    #
    @18
    cmul
    co
    #
    @7
    wcel
    #
    @3
    @42
    wceq
    #
    cR
    @24
    cif
    #
    cC
    cmin
    co
    #
    @3
    cdiv
    co
    #
    @28
    cmul
    co
    #
    @8
    wcel
    #
    wa
    #
    @9
    wa
    #
    wi
    @37
    @38
    wi
    vi
    cU
    @32
    @37
    @38
    vi
    @37
    vi
    nfv
    @31
    @9
    vi
    @20
    @30
    vi
    vi
    @19
    @7
    vi
    @17
    @18
    cmul
    vi
    @16
    @4
    cdiv
    vi
    @15
    cC
    cmin
    @12
    vi
    @13
    @14
    @12
    vi
    nfv
    vi
    cU
    cL
    nfcsb1v
    vi
    @14
    nfcv
    nfif
    vi
    cmin
    nfcv
    #
    vi
    cC
    nfcv
    #
    nfov
    vi
    cdiv
    nfcv
    #
    vi
    @4
    nfcv
    nfov
    vi
    cmul
    nfcv
    #
    vi
    @18
    nfcv
    nfov
    nfel1
    vi
    @29
    @8
    vi
    @27
    @28
    cmul
    vi
    @26
    @3
    cdiv
    vi
    @25
    cC
    cmin
    @22
    vi
    @23
    @24
    @22
    vi
    nfv
    vi
    cU
    cR
    nfcsb1v
    vi
    @24
    nfcv
    nfif
    @66
    @67
    nfov
    @68
    vi
    @3
    nfcv
    nfov
    @69
    vi
    @28
    nfcv
    nfov
    nfel1
    nfan
    @9
    vi
    nfv
    nfan
    nfim
    @39
    cU
    wceq
    #
    @47
    @37
    @65
    @38
    @70
    @41
    @34
    @46
    @36
    @70
    @40
    @33
    @2
    @39
    cU
    @32
    eleq1
    anbi2d
    @70
    @45
    @35
    @5
    @70
    @42
    @21
    @44
    @11
    cioo
    @39
    cU
    cQ
    fveq2
    #
    @70
    @43
    @10
    cQ
    @39
    cU
    c1
    caddc
    oveq1
    fveq2d
    #
    oveq12d
    sseq2d
    anbi12d
    @70
    @64
    @31
    @9
    @70
    @57
    @20
    @63
    @30
    @70
    @56
    @19
    @7
    @70
    @55
    @17
    @18
    cmul
    @70
    @54
    @16
    @4
    cdiv
    @70
    @53
    @15
    cC
    cmin
    @70
    @52
    @12
    cL
    @13
    @14
    @70
    @44
    @11
    @4
    @72
    eqeq2d
    vi
    cU
    cL
    csbeq1a
    ifbieq1d
    oveq1d
    oveq1d
    oveq1d
    eleq1d
    @70
    @62
    @29
    @8
    @70
    @61
    @27
    @28
    cmul
    @70
    @60
    @26
    @3
    cdiv
    @70
    @59
    @25
    cC
    cmin
    @70
    @58
    @22
    cR
    @23
    @24
    @70
    @42
    @21
    @3
    @71
    eqeq2d
    vi
    cU
    cR
    csbeq1a
    ifbieq1d
    oveq1d
    oveq1d
    oveq1d
    eleq1d
    anbi12d
    anbi1d
    imbi12d
    wph
    @47
    cA
    cB
    cC
    @56
    cP
    cQ
    cR
    cS
    cT
    vf
    vi
    vj
    vm
    @62
    cF
    cL
    cM
    cN
    cO
    cV
    cX
    vs
    vp
    fourierdlem86.f
    fourierdlem86.xre
    fourierdlem86.p
    fourierdlem86.m
    fourierdlem86.v
    fourierdlem86.fcn
    fourierdlem86.r
    fourierdlem86.l
    fourierdlem86.a
    fourierdlem86.b
    fourierdlem86.altb
    fourierdlem86.ab
    fourierdlem86.n0
    fourierdlem86.c
    fourierdlem86.o
    fourierdlem86.q
    fourierdlem86.t
    fourierdlem86.n
    fourierdlem86.s
    @56
    eqid
    @62
    eqid
    @47
    biid
    fourierdlem76
    vtoclg1f
    sylc
    #
    simpld
    #
    simpld
    syl5eqel
    @2
    cE
    @29
    @8
    fourierdlem86.e
    @2
    @20
    @30
    @74
    simprd
    syl5eqel
    @2
    @31
    @9
    @73
    simprd
    jca31
end
