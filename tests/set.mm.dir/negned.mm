include "cneg.mm"
include "wne.mm"
include "neg11ad.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem negned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume negned.2: |- ( ph -> B e. CC )
  assume negned.3: |- ( ph -> A =/= B )


  assert |- ( ph -> -u A =/= -u B )

  proof
    wph
    cA
    cneg
    #
    cB
    cneg
    #
    wne
    cA
    cB
    wne
    negned.3
    wph
    @0
    @1
    cA
    cB
    wph
    cA
    cB
    negidd.1
    negned.2
    neg11ad
    necon3bid
    mpbird
end
