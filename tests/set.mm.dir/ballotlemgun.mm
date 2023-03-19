include "cun.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "indir.mm"
include "fveq2i.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "infi.mm"
include "syl.mm"
include "ineq1d.mm"
include "inindir.mm"
include "0in.mm"
include "3eqtr3g.mm"
include "hashun.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "difundir.mm"
include "diffi.mm"
include "difeq1d.mm"
include "difindir.mm"
include "0dif.mm"
include "oveq12d.mm"
include "cn0.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0cnd.mm"
include "addsub4d.mm"
include "eqtrd.mm"
include "unfi.mm"
include "syl2anc.mm"
include "ballotlemgval.mm"
include "3eqtr4d.mm"

theorem ballotlemgun
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let vc: setvar c
  let cC: class C
  let cJ: class J
  let vj: setvar j
  let vd: setvar d
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )
  assume ballotlemg: |- .^ = ( u e. Fin , v e. Fin |-> ( ( # ` ( v i^i u ) ) - ( # ` ( v \ u ) ) ) )
  assume ballotlemgun.1: |- ( ph -> U e. Fin )
  assume ballotlemgun.2: |- ( ph -> V e. Fin )
  assume ballotlemgun.3: |- ( ph -> W e. Fin )
  assume ballotlemgun.4: |- ( ph -> ( V i^i W ) = (/) )

  disjoint u v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint W u
  disjoint W v
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint C u
  disjoint C v
  disjoint J u
  disjoint J v
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint C i
  disjoint C k
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint J k
  disjoint D i
  disjoint D k
  assert |- ( ph -> ( U .^ ( V u. W ) ) = ( ( U .^ V ) + ( U .^ W ) ) )

  proof
    wph
    cV
    cW
    cun
    #
    cU
    cin
    #
    chash
    cfv
    #
    @0
    cU
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    cV
    cU
    cin
    #
    chash
    cfv
    #
    cV
    cU
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    cW
    cU
    cin
    #
    chash
    cfv
    #
    cW
    cU
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    caddc
    co
    #
    cU
    @0
    c.ex
    co
    #
    cU
    cV
    c.ex
    co
    #
    cU
    cW
    c.ex
    co
    #
    caddc
    co
    wph
    @5
    @7
    @12
    caddc
    co
    #
    @9
    @14
    caddc
    co
    #
    cmin
    co
    @16
    wph
    @2
    @20
    @4
    @21
    cmin
    wph
    @2
    @6
    @11
    cun
    #
    chash
    cfv
    #
    @20
    @1
    @22
    chash
    cV
    cW
    cU
    indir
    fveq2i
    wph
    @6
    cfn
    wcel
    #
    @11
    cfn
    wcel
    #
    @6
    @11
    cin
    #
    c0
    wceq
    @23
    @20
    wceq
    wph
    cV
    cfn
    wcel
    #
    @24
    ballotlemgun.2
    cV
    cU
    infi
    #
    syl
    wph
    cW
    cfn
    wcel
    #
    @25
    ballotlemgun.3
    cW
    cU
    infi
    #
    syl
    wph
    cV
    cW
    cin
    #
    cU
    cin
    c0
    cU
    cin
    @26
    c0
    wph
    @31
    c0
    cU
    ballotlemgun.4
    ineq1d
    cV
    cW
    cU
    inindir
    cU
    0in
    3eqtr3g
    @6
    @11
    hashun
    syl3anc
    syl5eq
    wph
    @4
    @8
    @13
    cun
    #
    chash
    cfv
    #
    @21
    @3
    @32
    chash
    cV
    cW
    cU
    difundir
    fveq2i
    wph
    @8
    cfn
    wcel
    #
    @13
    cfn
    wcel
    #
    @8
    @13
    cin
    #
    c0
    wceq
    @33
    @21
    wceq
    wph
    @27
    @34
    ballotlemgun.2
    cV
    cU
    diffi
    #
    syl
    wph
    @29
    @35
    ballotlemgun.3
    cW
    cU
    diffi
    #
    syl
    wph
    @31
    cU
    cdif
    c0
    cU
    cdif
    @36
    c0
    wph
    @31
    c0
    cU
    ballotlemgun.4
    difeq1d
    cV
    cW
    cU
    difindir
    cU
    0dif
    3eqtr3g
    @8
    @13
    hashun
    syl3anc
    syl5eq
    oveq12d
    wph
    @7
    @12
    @9
    @14
    wph
    @7
    wph
    @27
    @24
    @7
    cn0
    wcel
    ballotlemgun.2
    @28
    @6
    hashcl
    3syl
    nn0cnd
    wph
    @12
    wph
    @29
    @25
    @12
    cn0
    wcel
    ballotlemgun.3
    @30
    @11
    hashcl
    3syl
    nn0cnd
    wph
    @9
    wph
    @27
    @34
    @9
    cn0
    wcel
    ballotlemgun.2
    @37
    @8
    hashcl
    3syl
    nn0cnd
    wph
    @14
    wph
    @29
    @35
    @14
    cn0
    wcel
    ballotlemgun.3
    @38
    @13
    hashcl
    3syl
    nn0cnd
    addsub4d
    eqtrd
    wph
    cU
    cfn
    wcel
    #
    @0
    cfn
    wcel
    #
    @17
    @5
    wceq
    ballotlemgun.1
    wph
    @27
    @29
    @40
    ballotlemgun.2
    ballotlemgun.3
    cV
    cW
    unfi
    syl2anc
    vx
    vv
    vu
    cP
    cR
    cS
    cU
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    @0
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemg
    ballotlemgval
    syl2anc
    wph
    @18
    @10
    @19
    @15
    caddc
    wph
    @39
    @27
    @18
    @10
    wceq
    ballotlemgun.1
    ballotlemgun.2
    vx
    vv
    vu
    cP
    cR
    cS
    cU
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    cV
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemg
    ballotlemgval
    syl2anc
    wph
    @39
    @29
    @19
    @15
    wceq
    ballotlemgun.1
    ballotlemgun.3
    vx
    vv
    vu
    cP
    cR
    cS
    cU
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    cW
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemg
    ballotlemgval
    syl2anc
    oveq12d
    3eqtr4d
end
