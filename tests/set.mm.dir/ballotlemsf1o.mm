include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ballotlemsval.mm"
include "wa.mm"
include "ballotlemsv.mm"
include "ballotlemsdom.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "oveq2.mm"
include "id.mm"
include "breq1.mm"
include "cc.mm"
include "cz.mm"
include "cc0.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfzelz.mm"
include "peano2zd.mm"
include "syl.mm"
include "zcnd.mm"
include "adantr.mm"
include "ad2antll.mm"
include "nncand.mm"
include "eqcomd.mm"
include "cn.mm"
include "elfznn.mm"
include "ltesubnnd.mm"
include "vex.mm"
include "a1i.mm"
include "ovexd.mm"
include "ifeqeqx.mm"
include "ad2antrl.mm"
include "simplrl.mm"
include "impbida.mm"
include "f1o3d.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "simprd.mm"
include "3eqtr4rd.mm"
include "jca.mm"

theorem ballotlemsf1o
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
  let cJ: class J
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )

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
  assert |- ( C e. ( O \ E ) -> ( ( S ` C ) : ( 1 ... ( M + N ) ) -1-1-onto-> ( 1 ... ( M + N ) ) /\ `' ( S ` C ) = ( S ` C ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    @2
    cC
    cS
    cfv
    #
    wf1o
    #
    @3
    ccnv
    #
    @3
    wceq
    @0
    @4
    @5
    vj
    @2
    vj
    cv
    #
    cC
    cI
    cfv
    #
    cle
    wbr
    #
    @7
    c1
    caddc
    co
    #
    @6
    cmin
    co
    #
    @6
    cif
    #
    cmpt
    #
    wceq
    #
    @0
    vi
    vj
    @2
    @2
    vi
    cv
    #
    @7
    cle
    wbr
    #
    @9
    @14
    cmin
    co
    #
    @14
    cif
    #
    @11
    @3
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
    ballotlemsval
    #
    @0
    @14
    @2
    wcel
    #
    wa
    @14
    @3
    cfv
    @17
    @2
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @14
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
    ballotlemsv
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @14
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
    ballotlemsdom
    eqeltrrd
    @0
    @6
    @2
    wcel
    #
    wa
    @6
    @3
    cfv
    @11
    @2
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @6
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
    ballotlemsv
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @6
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
    ballotlemsdom
    eqeltrrd
    @0
    @19
    @20
    wa
    #
    wa
    #
    @14
    @11
    wceq
    @6
    @17
    wceq
    @22
    @8
    @15
    @10
    @7
    cle
    wbr
    #
    vi
    @16
    @14
    @9
    @10
    cmin
    co
    #
    cvv
    cvv
    @10
    @6
    vj
    @14
    @10
    @9
    cmin
    oveq2
    @14
    @6
    wceq
    #
    id
    #
    @14
    @10
    @7
    cle
    breq1
    @14
    @6
    @7
    cle
    breq1
    #
    @22
    @24
    @6
    @22
    @9
    @6
    @0
    @9
    cc
    wcel
    @21
    @0
    @9
    @0
    @7
    @2
    wcel
    #
    @9
    cz
    wcel
    @0
    @28
    @7
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
    #
    @28
    @7
    @7
    c1
    @1
    elfzelz
    #
    peano2zd
    syl
    zcnd
    adantr
    #
    @20
    @6
    cc
    wcel
    @0
    @19
    @20
    @6
    @6
    c1
    @1
    elfzelz
    zcnd
    ad2antll
    nncand
    eqcomd
    @22
    @23
    @8
    @22
    @7
    @6
    @0
    @7
    cz
    wcel
    #
    @21
    @0
    @28
    @32
    @29
    @30
    syl
    adantr
    #
    @20
    @6
    cn
    wcel
    @0
    @19
    @6
    @1
    elfznn
    ad2antll
    ltesubnnd
    adantr
    @6
    cvv
    wcel
    @22
    vj
    vex
    a1i
    @22
    @9
    @6
    cmin
    ovexd
    ifeqeqx
    @22
    @15
    @8
    @16
    @7
    cle
    wbr
    vj
    @10
    @6
    @9
    @16
    cmin
    co
    #
    cvv
    cvv
    @16
    @14
    vi
    @6
    @16
    @9
    cmin
    oveq2
    @6
    @14
    wceq
    id
    @6
    @16
    @7
    cle
    breq1
    @6
    @14
    @7
    cle
    breq1
    @22
    @34
    @14
    @22
    @9
    @14
    @31
    @19
    @14
    cc
    wcel
    @0
    @20
    @19
    @14
    @14
    c1
    @1
    elfzelz
    zcnd
    ad2antrl
    nncand
    eqcomd
    @22
    @15
    wa
    #
    @7
    @14
    @22
    @32
    @15
    @33
    adantr
    @35
    @19
    @14
    cn
    wcel
    @0
    @19
    @20
    @15
    simplrl
    @14
    @1
    elfznn
    syl
    ltesubnnd
    @14
    cvv
    wcel
    @22
    vi
    vex
    a1i
    @22
    @9
    @14
    cmin
    ovexd
    ifeqeqx
    impbida
    f1o3d
    #
    simpld
    @0
    vi
    @2
    @17
    cmpt
    #
    @12
    @3
    @5
    @37
    @12
    wceq
    @0
    vi
    vj
    @2
    @17
    @11
    @25
    @15
    @8
    @16
    @14
    @10
    @6
    @27
    @14
    @6
    @9
    cmin
    oveq2
    @26
    ifbieq12d
    cbvmptv
    a1i
    @18
    @0
    @4
    @13
    @36
    simprd
    3eqtr4rd
    jca
end
