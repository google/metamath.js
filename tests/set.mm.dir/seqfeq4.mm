include "cseq.mm"
include "cfv.mm"
include "cid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "ovex.mm"
include "vex.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "cfz.mm"
include "mp1i.mm"
include "seqhomo.mm"
include "syl5eqr.mm"

theorem seqfeq4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  assume seqfeq4.m: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqfeq4.f: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. S )
  assume seqfeq4.cl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqfeq4.id: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) = ( x Q y ) )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint Q x
  disjoint Q y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( seq M ( Q , F ) ` N ) )

  proof
    wph
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    @1
    cid
    cfv
    #
    cN
    cQ
    cF
    cM
    cseq
    cfv
    @1
    cvv
    wcel
    @2
    @1
    wceq
    cN
    @0
    fvex
    @1
    cvv
    fvi
    ax-mp
    wph
    vx
    vy
    c.pl
    cQ
    cS
    cF
    cF
    cid
    cM
    cN
    seqfeq4.cl
    seqfeq4.f
    seqfeq4.m
    wph
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    wa
    @3
    @4
    c.pl
    co
    #
    @3
    @4
    cQ
    co
    @5
    cid
    cfv
    #
    @3
    cid
    cfv
    #
    @4
    cid
    cfv
    #
    cQ
    co
    seqfeq4.id
    @5
    cvv
    wcel
    @6
    @5
    wceq
    @3
    @4
    c.pl
    ovex
    @5
    cvv
    fvi
    ax-mp
    @7
    @3
    @8
    @4
    cQ
    @3
    cvv
    wcel
    @7
    @3
    wceq
    vx
    vex
    @3
    cvv
    fvi
    ax-mp
    @4
    cvv
    wcel
    @8
    @4
    wceq
    vy
    vex
    @4
    cvv
    fvi
    ax-mp
    oveq12i
    3eqtr4g
    @3
    cF
    cfv
    #
    cvv
    wcel
    @9
    cid
    cfv
    @9
    wceq
    wph
    @3
    cM
    cN
    cfz
    co
    wcel
    wa
    @3
    cF
    fvex
    @9
    cvv
    fvi
    mp1i
    seqhomo
    syl5eqr
end
