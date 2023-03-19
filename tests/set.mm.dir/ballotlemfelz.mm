include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "chash.mm"
include "cdif.mm"
include "cmin.mm"
include "cz.mm"
include "ballotlemfval.mm"
include "wcel.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "fzfi.mm"
include "inss1.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0zi.mm"
include "difss.mm"
include "zsubcl.mm"
include "syl6eqel.mm"

theorem ballotlemfelz
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
  assert |- ( ph -> ( ( F ` C ) ` J ) e. ZZ )

  proof
    wph
    cJ
    cC
    cF
    cfv
    cfv
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
    @0
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
    wph
    vx
    cC
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
    ballotlemfval.c
    ballotlemfval.j
    ballotlemfval
    @2
    cz
    wcel
    @4
    cz
    wcel
    @5
    cz
    wcel
    @2
    @1
    cfn
    wcel
    #
    @2
    cn0
    wcel
    @0
    cfn
    wcel
    #
    @1
    @0
    wss
    @6
    c1
    cJ
    fzfi
    #
    @0
    cC
    inss1
    @0
    @1
    ssfi
    mp2an
    @1
    hashcl
    ax-mp
    nn0zi
    @4
    @3
    cfn
    wcel
    #
    @4
    cn0
    wcel
    @7
    @3
    @0
    wss
    @9
    @8
    @0
    cC
    difss
    @0
    @3
    ssfi
    mp2an
    @3
    hashcl
    ax-mp
    nn0zi
    @2
    @4
    zsubcl
    mp2an
    syl6eqel
end
