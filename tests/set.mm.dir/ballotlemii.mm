include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "1e0p1.mm"
include "ax-1ne0.mm"
include "eqnetrri.mm"
include "neii.mm"
include "cmin.mm"
include "wn.mm"
include "wi.mm"
include "eldifi.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "ballotlemfp1.mm"
include "simprd.mm"
include "imp.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "ballotlemfval0.mm"
include "syl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "eqeq1d.mm"
include "mtbii.mm"
include "cfz.mm"
include "ballotlemiex.mm"
include "ad2antrr.mm"
include "wb.mm"
include "fveq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "mtand.mm"
include "neqned.mm"

theorem ballotlemii
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vd: setvar d
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )

  disjoint c k
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
  disjoint c y
  disjoint c z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ 1 e. C ) -> ( I ` C ) =/= 1 )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    c1
    cC
    wcel
    #
    wa
    #
    cC
    cI
    cfv
    #
    c1
    @2
    @3
    c1
    wceq
    #
    c1
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @2
    cc0
    c1
    caddc
    co
    #
    cc0
    wceq
    @7
    @8
    cc0
    c1
    @8
    cc0
    1e0p1
    ax-1ne0
    eqnetrri
    neii
    @2
    @8
    @6
    cc0
    @2
    @6
    c1
    c1
    cmin
    co
    #
    @5
    cfv
    #
    c1
    caddc
    co
    #
    cc0
    @5
    cfv
    #
    c1
    caddc
    co
    #
    @8
    @0
    @1
    @6
    @11
    wceq
    #
    @0
    @1
    wn
    @6
    @10
    c1
    cmin
    co
    wceq
    wi
    @1
    @14
    wi
    @0
    vx
    cC
    cP
    vi
    cF
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
    cC
    cO
    cE
    eldifi
    #
    c1
    cn
    wcel
    @0
    1nn
    a1i
    ballotlemfp1
    simprd
    imp
    @11
    @13
    wceq
    @2
    @10
    @12
    c1
    caddc
    @9
    cc0
    @5
    1m1e0
    fveq2i
    oveq1i
    a1i
    @2
    @12
    cc0
    c1
    caddc
    @0
    @12
    cc0
    wceq
    #
    @1
    @0
    cC
    cO
    wcel
    @16
    @15
    vx
    cC
    cP
    vi
    cF
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotlemfval0
    syl
    adantr
    oveq1d
    3eqtrrd
    eqeq1d
    mtbii
    @2
    @4
    wa
    @3
    @5
    cfv
    #
    cc0
    wceq
    #
    @7
    @0
    @18
    @1
    @4
    @0
    @3
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    wcel
    @18
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
    simprd
    ad2antrr
    @4
    @18
    @7
    wb
    @2
    @4
    @17
    @6
    cc0
    @3
    c1
    @5
    fveq2
    eqeq1d
    adantl
    mpbid
    mtand
    neqned
end
