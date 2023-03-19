include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wf1o.mm"
include "simpl.mm"
include "wceq.mm"
include "ballotlemsf1o.mm"
include "simpld.mm"
include "f1ofun.mm"
include "3syl.mm"
include "simpr.mm"
include "f1odm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "ballotlemsv.mm"
include "eleq1d.mm"
include "simprd.mm"
include "imaeq1d.mm"
include "ballotlemrval.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "syl.mm"
include "3bitr3rd.mm"

theorem ballotlemrv
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
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
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) -> ( J e. ( R ` C ) <-> if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) e. C ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    wcel
    #
    wa
    #
    cJ
    cC
    cS
    cfv
    #
    cfv
    #
    cC
    wcel
    #
    cJ
    @4
    ccnv
    #
    cC
    cima
    #
    wcel
    #
    cJ
    cC
    cI
    cfv
    #
    cle
    wbr
    @10
    c1
    caddc
    co
    cJ
    cmin
    co
    cJ
    cif
    #
    cC
    wcel
    cJ
    cC
    cR
    cfv
    #
    wcel
    #
    @3
    @4
    wfun
    #
    cJ
    @4
    cdm
    #
    wcel
    @6
    @9
    wb
    @3
    @0
    @1
    @1
    @4
    wf1o
    #
    @14
    @0
    @2
    simpl
    #
    @0
    @16
    @7
    @4
    wceq
    #
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
    #
    simpld
    #
    @1
    @1
    @4
    f1ofun
    3syl
    @3
    cJ
    @1
    @15
    @0
    @2
    simpr
    @3
    @0
    @16
    @15
    @1
    wceq
    @17
    @20
    @1
    @1
    @4
    f1odm
    3syl
    eleqtrrd
    cJ
    cC
    @4
    fvimacnv
    syl2anc
    @3
    @5
    @11
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
    ballotlemsv
    eleq1d
    @3
    @0
    @9
    @13
    wb
    @17
    @0
    @8
    @12
    cJ
    @0
    @8
    @4
    cC
    cima
    @12
    @0
    @7
    @4
    cC
    @0
    @16
    @18
    @19
    simprd
    imaeq1d
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
    ballotlemrval
    eqtr4d
    eleq2d
    syl
    3bitr3rd
end
