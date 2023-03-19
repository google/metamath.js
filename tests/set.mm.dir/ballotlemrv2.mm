include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cle.mm"
include "cmin.mm"
include "cif.mm"
include "wb.mm"
include "ballotlemrv.mm"
include "3adant3.mm"
include "wn.mm"
include "wa.mm"
include "cz.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "cc0.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "sseldi.mm"
include "adantr.mm"
include "zred.mm"
include "simpr.mm"
include "ltnled.mm"
include "biimp3a.mm"
include "iffalsed.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem ballotlemrv2
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
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ ( I ` C ) < J ) -> ( J e. ( R ` C ) <-> J e. C ) )

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
    #
    cfz
    co
    #
    wcel
    #
    cC
    cI
    cfv
    #
    cJ
    clt
    wbr
    #
    w3a
    #
    cJ
    cC
    cR
    cfv
    wcel
    #
    cJ
    @4
    cle
    wbr
    #
    @4
    c1
    caddc
    co
    cJ
    cmin
    co
    #
    cJ
    cif
    #
    cC
    wcel
    #
    cJ
    cC
    wcel
    @0
    @3
    @7
    @11
    wb
    @5
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
    ballotth.r
    ballotlemrv
    3adant3
    @6
    @10
    cJ
    cC
    @6
    @8
    @9
    cJ
    @0
    @3
    @5
    @8
    wn
    @0
    @3
    wa
    #
    @4
    cJ
    @12
    @4
    @0
    @4
    cz
    wcel
    @3
    @0
    @2
    cz
    @4
    @2
    c1
    cuz
    cfv
    cz
    c1
    @1
    fzssuz
    c1
    uzssz
    sstri
    #
    @0
    @4
    @2
    wcel
    @4
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
    sseldi
    adantr
    zred
    @12
    cJ
    @12
    @2
    cz
    cJ
    @13
    @0
    @3
    simpr
    sseldi
    zred
    ltnled
    biimp3a
    iffalsed
    eleq1d
    bitrd
end
