include "cneg.mm"
include "wceq.mm"
include "cc.mm"
include "negcld.mm"
include "eqeltrrd.mm"
include "negcon1d.mm"
include "mpbid.mm"

theorem negcon1ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume negcon1ad.2: |- ( ph -> -u A = B )


  assert |- ( ph -> -u B = A )

  proof
    wph
    cA
    cneg
    #
    cB
    wceq
    cB
    cneg
    cA
    wceq
    negcon1ad.2
    wph
    cA
    cB
    negidd.1
    wph
    @0
    cB
    cc
    negcon1ad.2
    wph
    cA
    negidd.1
    negcld
    eqeltrrd
    negcon1d
    mpbid
end
