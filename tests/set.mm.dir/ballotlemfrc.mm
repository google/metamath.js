include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cin.mm"
include "chash.mm"
include "cmin.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "caddc.mm"
include "wf1.mm"
include "wss.mm"
include "ccnv.mm"
include "ballotlemsf1o.mm"
include "simpld.mm"
include "f1of1.mm"
include "syl.mm"
include "adantr.mm"
include "cuz.mm"
include "cc0.mm"
include "ballotlemiex.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "fzss2.mm"
include "ssinss1.mm"
include "f1ores.mm"
include "ovex.mm"
include "inex1.mm"
include "f1oen.mm"
include "hasheni.mm"
include "3syl.mm"
include "ssdifssd.mm"
include "cvv.mm"
include "difexg.mm"
include "ax-mp.mm"
include "oveq12d.mm"
include "ballotlemro.mm"
include "cz.mm"
include "elfzelz.mm"
include "ballotlemfval.mm"
include "cfn.mm"
include "fzfi.mm"
include "eldifi.mm"
include "ballotlemelo.mm"
include "simplbi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "fzfid.mm"
include "ballotlemgval.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imain.mm"
include "ballotlemsima.mm"
include "ballotlemscr.mm"
include "ineq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "imadif.mm"
include "difeq12d.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem ballotlemfrc
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let cU: class U
  let cV: class V
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

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint I u
  disjoint I v
  disjoint J u
  disjoint J v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint J i
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
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint J k
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint D i
  disjoint D k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) -> ( ( F ` ( R ` C ) ) ` J ) = ( C .^ ( ( ( S ` C ) ` J ) ... ( I ` C ) ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cC
    cI
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    c1
    cJ
    cfz
    co
    #
    cC
    cR
    cfv
    #
    cin
    #
    chash
    cfv
    #
    @4
    @5
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    cC
    cS
    cfv
    #
    @6
    cima
    #
    chash
    cfv
    #
    @10
    @8
    cima
    #
    chash
    cfv
    #
    cmin
    co
    #
    cJ
    @5
    cF
    cfv
    cfv
    cC
    cJ
    @10
    cfv
    #
    @1
    cfz
    co
    #
    c.ex
    co
    #
    @3
    @7
    @12
    @9
    @14
    cmin
    @3
    @6
    @11
    @10
    @6
    cres
    #
    wf1o
    #
    @6
    @11
    cen
    wbr
    @7
    @12
    wceq
    @3
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    @22
    @10
    wf1
    #
    @6
    @22
    wss
    #
    @20
    @0
    @23
    @2
    @0
    @22
    @22
    @10
    wf1o
    #
    @23
    @0
    @25
    @10
    ccnv
    #
    @10
    wceq
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
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
    ballotlemsf1o
    simpld
    #
    @22
    @22
    @10
    f1of1
    syl
    adantr
    #
    @3
    @4
    @22
    wss
    #
    @24
    @3
    @21
    cJ
    cuz
    cfv
    #
    wcel
    #
    @29
    @3
    @21
    @1
    cuz
    cfv
    wcel
    #
    @1
    @30
    wcel
    #
    @31
    @3
    @1
    @22
    wcel
    #
    @32
    @0
    @34
    @2
    @0
    @34
    @1
    cC
    cF
    cfv
    cfv
    cc0
    wceq
    vx
    cC
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlemiex
    simpld
    adantr
    @1
    c1
    @21
    elfzuz3
    syl
    @2
    @33
    @0
    cJ
    c1
    @1
    elfzuz3
    adantl
    @1
    @21
    cJ
    uztrn
    syl2anc
    cJ
    c1
    @21
    fzss2
    syl
    #
    @4
    @5
    @22
    ssinss1
    syl
    @22
    @22
    @6
    @10
    f1ores
    syl2anc
    @6
    @11
    @19
    @4
    @5
    c1
    cJ
    cfz
    ovex
    #
    inex1
    f1oen
    @6
    @11
    hasheni
    3syl
    @3
    @8
    @13
    @10
    @8
    cres
    #
    wf1o
    #
    @8
    @13
    cen
    wbr
    @9
    @14
    wceq
    @3
    @23
    @8
    @22
    wss
    @38
    @28
    @3
    @4
    @22
    @5
    @35
    ssdifssd
    @22
    @22
    @8
    @10
    f1ores
    syl2anc
    @8
    @13
    @37
    @4
    cvv
    wcel
    @8
    cvv
    wcel
    @36
    @4
    @5
    cvv
    difexg
    ax-mp
    f1oen
    @8
    @13
    hasheni
    3syl
    oveq12d
    @3
    vx
    @5
    cP
    vi
    cF
    cJ
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    @0
    @5
    cO
    wcel
    @2
    vx
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
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
    ballotlemro
    adantr
    @2
    cJ
    cz
    wcel
    @0
    cJ
    c1
    @1
    elfzelz
    adantl
    ballotlemfval
    @3
    @18
    @17
    cC
    cin
    #
    chash
    cfv
    #
    @17
    cC
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    #
    @15
    @3
    cC
    cfn
    wcel
    #
    @17
    cfn
    wcel
    @18
    @43
    wceq
    @3
    @22
    cfn
    wcel
    cC
    @22
    wss
    #
    @44
    c1
    @21
    fzfi
    @0
    @45
    @2
    @0
    cC
    cO
    wcel
    #
    @45
    cC
    cO
    cE
    eldifi
    @46
    @45
    cC
    chash
    cfv
    cM
    wceq
    cC
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    simplbi
    syl
    adantr
    @22
    cC
    ssfi
    sylancr
    @3
    @16
    @1
    fzfid
    vx
    vv
    vu
    cP
    cR
    cS
    cC
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    @17
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
    @3
    @12
    @40
    @14
    @42
    cmin
    @3
    @11
    @39
    chash
    @3
    @11
    @10
    @4
    cima
    #
    @10
    @5
    cima
    #
    cin
    #
    @39
    @0
    @11
    @49
    wceq
    #
    @2
    @0
    @25
    @26
    wfun
    #
    @50
    @27
    @25
    @22
    @22
    @10
    wfo
    @51
    @22
    @22
    @10
    dff1o3
    simprbi
    #
    @4
    @5
    @10
    imain
    3syl
    adantr
    @3
    @47
    @17
    @48
    cC
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cJ
    cM
    cN
    cO
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
    ballotlemsima
    #
    @0
    @48
    cC
    wceq
    @2
    vx
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
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
    ballotlemscr
    adantr
    #
    ineq12d
    eqtrd
    fveq2d
    @3
    @13
    @41
    chash
    @3
    @13
    @47
    @48
    cdif
    #
    @41
    @0
    @13
    @55
    wceq
    #
    @2
    @0
    @25
    @51
    @56
    @27
    @52
    @4
    @5
    @10
    imadif
    3syl
    adantr
    @3
    @47
    @17
    @48
    cC
    @53
    @54
    difeq12d
    eqtrd
    fveq2d
    oveq12d
    eqtr4d
    3eqtr4d
end
