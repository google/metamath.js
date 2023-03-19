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
include "wceq.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqfveq.mm"
include "eqfnfvd.mm"

theorem seqfeq
  let wph: wff ph
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let vx: setvar x
  assume seqfeq.1: |- ( ph -> M e. ZZ )
  assume seqfeq.2: |- ( ( ph /\ k e. ( ZZ>= ` M ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint k x
  disjoint F x
  disjoint G x
  disjoint M x
  disjoint .+ x
  disjoint ph x
  assert |- ( ph -> seq M ( .+ , F ) = seq M ( .+ , G ) )

  proof
    wph
    vx
    cM
    cuz
    cfv
    #
    c.pl
    cF
    cM
    cseq
    #
    c.pl
    cG
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
    seqfeq.1
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
    seqfeq.1
    c.pl
    cG
    cM
    seqfn
    syl
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    c.pl
    vk
    cF
    cG
    cM
    @4
    wph
    @5
    simpr
    wph
    vk
    cv
    #
    cM
    @4
    cfz
    co
    wcel
    #
    @6
    cF
    cfv
    @6
    cG
    cfv
    wceq
    #
    @5
    @7
    wph
    @6
    @0
    wcel
    @8
    @6
    cM
    @4
    elfzuz
    seqfeq.2
    sylan2
    adantlr
    seqfveq
    eqfnfvd
end
