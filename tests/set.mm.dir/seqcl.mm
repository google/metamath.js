include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cuz.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "wss.mm"
include "eluzel2.mm"
include "fzp1ss.mm"
include "sselda.mm"
include "syldan.mm"
include "seqcl2.mm"

theorem seqcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  assume seqcl.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqcl.2: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. S )
  assume seqcl.3: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )

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
  disjoint N x
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) e. S )

  proof
    wph
    vx
    vy
    cS
    cS
    c.pl
    cF
    cM
    cN
    wph
    cM
    cM
    cN
    cfz
    co
    #
    wcel
    #
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
    @0
    wral
    cM
    cF
    cfv
    #
    cS
    wcel
    #
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @1
    seqcl.1
    cM
    cN
    eluzfz1
    syl
    wph
    @4
    vx
    @0
    seqcl.2
    ralrimiva
    @4
    @6
    vx
    cM
    @0
    @2
    cM
    wceq
    @3
    @5
    cS
    @2
    cM
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    seqcl.3
    seqcl.1
    wph
    @2
    cM
    c1
    caddc
    co
    cN
    cfz
    co
    #
    wcel
    @2
    @0
    wcel
    @4
    wph
    @8
    @0
    @2
    wph
    cM
    cz
    wcel
    #
    @8
    @0
    wss
    wph
    @7
    @9
    seqcl.1
    cM
    cN
    eluzel2
    syl
    cM
    cN
    fzp1ss
    syl
    sselda
    seqcl.2
    syldan
    seqcl2
end
