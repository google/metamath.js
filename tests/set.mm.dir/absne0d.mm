include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "abs00ad.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem absne0d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )
  assume absne0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( abs ` A ) =/= 0 )

  proof
    wph
    cA
    cabs
    cfv
    #
    cc0
    wne
    cA
    cc0
    wne
    absne0d.2
    wph
    @0
    cc0
    cA
    cc0
    wph
    cA
    abscld.1
    abs00ad
    necon3bid
    mpbird
end
