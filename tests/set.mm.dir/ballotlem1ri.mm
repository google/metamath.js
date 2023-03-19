include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "cuz.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnuz.mm"
include "eleqtri.mm"
include "eluzfz1.mm"
include "mp1i.mm"
include "cc0.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfzle1.mm"
include "syl.mm"
include "ballotlemrv1.mm"
include "mpd3an23.mm"
include "cz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem ballotlem1ri
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
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
  let cJ: class J
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
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint R k
  disjoint c x
  disjoint C x
  disjoint F x
  disjoint M x
  disjoint N x
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
  disjoint J k
  disjoint D i
  disjoint D k
  disjoint S d
  assert |- ( C e. ( O \ E ) -> ( 1 e. ( R ` C ) <-> ( I ` C ) e. C ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    c1
    cC
    cR
    cfv
    wcel
    #
    cC
    cI
    cfv
    #
    c1
    caddc
    co
    c1
    cmin
    co
    #
    cC
    wcel
    #
    @2
    cC
    wcel
    @0
    c1
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
    c1
    @2
    cle
    wbr
    #
    @1
    @4
    wb
    @5
    c1
    cuz
    cfv
    #
    wcel
    @7
    @0
    @5
    cn
    @9
    cM
    cn
    wcel
    cN
    cn
    wcel
    @5
    cn
    wcel
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    nnuz
    eleqtri
    c1
    @5
    eluzfz1
    mp1i
    @0
    @2
    @6
    wcel
    #
    @8
    @0
    @10
    @2
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
    @2
    c1
    @5
    elfzle1
    syl
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
    c1
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
    ballotlemrv1
    mpd3an23
    @0
    @3
    @2
    cC
    @0
    @2
    c1
    @0
    @2
    @0
    @10
    @2
    cz
    wcel
    @11
    @2
    c1
    @5
    elfzelz
    syl
    zcnd
    @0
    1cnd
    pncand
    eleq1d
    bitrd
end
