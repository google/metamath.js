include "cdif.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "eldifi.mm"
include "cn.mm"
include "a1i.mm"
include "nnaddcld.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "wrex.mm"
include "ballotlemodife.mm"
include "simprbi.mm"
include "cmin.mm"
include "clt.mm"
include "nnrei.mm"
include "posdifi.mm"
include "mpbi.mm"
include "wceq.mm"
include "ballotlemfmpn.mm"
include "syl.mm"
include "syl5breqr.mm"
include "ballotlemfc0.mm"

theorem ballotlem5
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M

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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  assert |- ( C e. ( O \ E ) -> E. k e. ( 1 ... ( M + N ) ) ( ( F ` C ) ` k ) = 0 )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    vx
    cC
    cP
    vi
    vk
    cF
    cM
    cN
    caddc
    co
    #
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
    @0
    cM
    cN
    cM
    cn
    wcel
    @0
    ballotth.m
    a1i
    cN
    cn
    wcel
    @0
    ballotth.n
    a1i
    nnaddcld
    @0
    cC
    cO
    wcel
    #
    vi
    cv
    cC
    cF
    cfv
    #
    cfv
    cc0
    cle
    wbr
    vi
    c1
    @1
    cfz
    co
    wrex
    vx
    cC
    cP
    vi
    cE
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
    ballotth.e
    ballotlemodife
    simprbi
    @0
    cc0
    cM
    cN
    cmin
    co
    #
    @1
    @4
    cfv
    #
    clt
    cN
    cM
    clt
    wbr
    cc0
    @5
    clt
    wbr
    ballotth.mgtn
    cN
    cM
    cN
    ballotth.n
    nnrei
    cM
    ballotth.m
    nnrei
    posdifi
    mpbi
    @0
    @3
    @6
    @5
    wceq
    @2
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
    ballotlemfmpn
    syl
    syl5breqr
    ballotlemfc0
end
