include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cuz.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "peano2uzr.mm"
include "sylan.mm"
include "syldan.mm"
include "seqf2.mm"

theorem seqf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume seqf.1: |- Z = ( ZZ>= ` M )
  assume seqf.2: |- ( ph -> M e. ZZ )
  assume seqf.3: |- ( ( ph /\ x e. Z ) -> ( F ` x ) e. S )
  assume seqf.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint Z x
  assert |- ( ph -> seq M ( .+ , F ) : Z --> S )

  proof
    wph
    vx
    vy
    cS
    cS
    c.pl
    cF
    cM
    cZ
    wph
    cM
    cZ
    wcel
    vx
    cv
    #
    cF
    cfv
    #
    cS
    wcel
    #
    vx
    cZ
    wral
    cM
    cF
    cfv
    #
    cS
    wcel
    #
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    cM
    @5
    wcel
    seqf.2
    cM
    uzid
    syl
    seqf.1
    syl6eleqr
    wph
    @2
    vx
    cZ
    seqf.3
    ralrimiva
    @2
    @4
    vx
    cM
    cZ
    @0
    cM
    wceq
    @1
    @3
    cS
    @0
    cM
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    seqf.4
    seqf.1
    seqf.2
    wph
    @0
    cM
    c1
    caddc
    co
    cuz
    cfv
    wcel
    #
    @0
    cZ
    wcel
    @2
    wph
    @7
    wa
    @0
    @5
    cZ
    wph
    @6
    @7
    @0
    @5
    wcel
    seqf.2
    cM
    @0
    peano2uzr
    sylan
    seqf.1
    syl6eleqr
    seqf.3
    syldan
    seqf2
end
