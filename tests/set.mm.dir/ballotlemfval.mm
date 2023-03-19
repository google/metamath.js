include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "cmin.mm"
include "cz.mm"
include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "difeq2d.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "ineq2.mm"
include "difeq2.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "eqtr4i.mm"
include "zex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveq2.mm"
include "ineq1d.mm"
include "difeq1d.mm"
include "adantl.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem ballotlemfval
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vb: setvar b
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotlemfval.c: |- ( ph -> C e. O )
  assume ballotlemfval.j: |- ( ph -> J e. ZZ )

  disjoint J i
  disjoint i ph
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint C i
  disjoint O b
  disjoint C b
  disjoint b c
  disjoint b i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( ph -> ( ( F ` C ) ` J ) = ( ( # ` ( ( 1 ... J ) i^i C ) ) - ( # ` ( ( 1 ... J ) \ C ) ) ) )

  proof
    wph
    vi
    cJ
    c1
    vi
    cv
    #
    cfz
    co
    #
    cC
    cin
    #
    chash
    cfv
    #
    @1
    cC
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    c1
    cJ
    cfz
    co
    #
    cC
    cin
    #
    chash
    cfv
    #
    @7
    cC
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    cz
    cC
    cF
    cfv
    #
    cvv
    wph
    cC
    cO
    wcel
    @13
    vi
    cz
    @6
    cmpt
    #
    wceq
    ballotlemfval.c
    vb
    cC
    vi
    cz
    @1
    vb
    cv
    #
    cin
    #
    chash
    cfv
    #
    @1
    @15
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    @14
    cO
    cF
    @15
    cC
    wceq
    #
    vi
    cz
    @20
    @6
    @22
    @0
    cz
    wcel
    #
    wa
    #
    @17
    @3
    @19
    @5
    cmin
    @24
    @16
    @2
    chash
    @24
    @15
    cC
    @1
    @22
    @23
    simpl
    #
    ineq2d
    fveq2d
    @24
    @18
    @4
    chash
    @24
    @15
    cC
    @1
    @25
    difeq2d
    fveq2d
    oveq12d
    mpteq2dva
    cF
    vc
    cO
    vi
    cz
    @1
    vc
    cv
    #
    cin
    #
    chash
    cfv
    #
    @1
    @26
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cmpt
    vb
    cO
    @21
    cmpt
    ballotth.f
    vb
    vc
    cO
    @21
    @32
    @15
    @26
    wceq
    #
    vi
    cz
    @20
    @31
    @33
    @17
    @28
    @19
    @30
    cmin
    @33
    @16
    @27
    chash
    @15
    @26
    @1
    ineq2
    fveq2d
    @33
    @18
    @29
    chash
    @15
    @26
    @1
    difeq2
    fveq2d
    oveq12d
    mpteq2dv
    cbvmptv
    eqtr4i
    vi
    cz
    @6
    zex
    mptex
    fvmpt
    syl
    @0
    cJ
    wceq
    #
    @6
    @12
    wceq
    wph
    @34
    @3
    @9
    @5
    @11
    cmin
    @34
    @2
    @8
    chash
    @34
    @1
    @7
    cC
    @0
    cJ
    c1
    cfz
    oveq2
    #
    ineq1d
    fveq2d
    @34
    @4
    @10
    chash
    @34
    @1
    @7
    cC
    @35
    difeq1d
    fveq2d
    oveq12d
    adantl
    ballotlemfval.j
    wph
    @9
    @11
    cmin
    ovexd
    fvmptd
end
