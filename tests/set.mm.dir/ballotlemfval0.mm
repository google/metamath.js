include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "chash.mm"
include "cdif.mm"
include "cmin.mm"
include "id.mm"
include "0zd.mm"
include "ballotlemfval.mm"
include "c0.mm"
include "fz10.mm"
include "ineq1i.mm"
include "incom.mm"
include "in0.mm"
include "3eqtr2i.mm"
include "fveq2i.mm"
include "hash0.mm"
include "eqtri.mm"
include "difeq1i.mm"
include "0dif.mm"
include "oveq12i.mm"
include "0m0e0.mm"
include "syl6eq.mm"

theorem ballotlemfval0
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )

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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( C e. O -> ( ( F ` C ) ` 0 ) = 0 )

  proof
    cC
    cO
    wcel
    #
    cc0
    cC
    cF
    cfv
    cfv
    c1
    cc0
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
    cc0
    @0
    vx
    cC
    cP
    vi
    cF
    cc0
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
    id
    @0
    0zd
    ballotlemfval
    @6
    cc0
    cc0
    cmin
    co
    cc0
    @3
    cc0
    @5
    cc0
    cmin
    @3
    c0
    chash
    cfv
    #
    cc0
    @2
    c0
    chash
    @2
    c0
    cC
    cin
    cC
    c0
    cin
    c0
    @1
    c0
    cC
    fz10
    ineq1i
    cC
    c0
    incom
    cC
    in0
    3eqtr2i
    fveq2i
    hash0
    eqtri
    @5
    @7
    cc0
    @4
    c0
    chash
    @4
    c0
    cC
    cdif
    c0
    @1
    c0
    cC
    fz10
    difeq1i
    cC
    0dif
    eqtri
    fveq2i
    hash0
    eqtri
    oveq12i
    0m0e0
    eqtri
    syl6eq
end
