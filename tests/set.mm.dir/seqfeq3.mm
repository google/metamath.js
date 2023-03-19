include "cuz.mm"
include "cfv.mm"
include "cseq.mm"
include "cz.mm"
include "wcel.mm"
include "wfn.mm"
include "seqfn.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "simpr.mm"
include "cfz.mm"
include "co.mm"
include "simpll.mm"
include "elfzuz.mm"
include "adantl.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "wceq.mm"
include "seqfeq4.mm"
include "eqfnfvd.mm"

theorem seqfeq3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cM: class M
  let va: setvar a
  assume seqfeq3.m: |- ( ph -> M e. ZZ )
  assume seqfeq3.f: |- ( ( ph /\ x e. ( ZZ>= ` M ) ) -> ( F ` x ) e. S )
  assume seqfeq3.cl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqfeq3.id: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) = ( x Q y ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint .+ x
  disjoint .+ y
  disjoint Q x
  disjoint Q y
  disjoint S x
  disjoint S y
  disjoint a ph
  disjoint a x
  disjoint a y
  disjoint F a
  disjoint M a
  disjoint .+ a
  disjoint Q a
  assert |- ( ph -> seq M ( .+ , F ) = seq M ( Q , F ) )

  proof
    wph
    va
    cM
    cuz
    cfv
    #
    c.pl
    cF
    cM
    cseq
    #
    cQ
    cF
    cM
    cseq
    #
    wph
    cM
    cz
    wcel
    #
    @1
    @0
    wfn
    seqfeq3.m
    c.pl
    cF
    cM
    seqfn
    syl
    wph
    @3
    @2
    @0
    wfn
    seqfeq3.m
    cQ
    cF
    cM
    seqfn
    syl
    wph
    va
    cv
    #
    @0
    wcel
    #
    wa
    #
    vx
    vy
    c.pl
    cQ
    cS
    cF
    cM
    @4
    wph
    @5
    simpr
    @6
    vx
    cv
    #
    cM
    @4
    cfz
    co
    wcel
    #
    wa
    wph
    @7
    @0
    wcel
    #
    @7
    cF
    cfv
    cS
    wcel
    wph
    @5
    @8
    simpll
    @8
    @9
    @6
    @7
    cM
    @4
    elfzuz
    adantl
    seqfeq3.f
    syl2anc
    wph
    @7
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @7
    @10
    c.pl
    co
    #
    cS
    wcel
    @5
    seqfeq3.cl
    adantlr
    wph
    @11
    @12
    @7
    @10
    cQ
    co
    wceq
    @5
    seqfeq3.id
    adantlr
    seqfeq4
    eqfnfvd
end
