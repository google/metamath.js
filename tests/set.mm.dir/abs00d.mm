include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "abs00ad.mm"
include "mpbid.mm"

theorem abs00d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )
  assume abs00d.2: |- ( ph -> ( abs ` A ) = 0 )


  assert |- ( ph -> A = 0 )

  proof
    wph
    cA
    cabs
    cfv
    cc0
    wceq
    cA
    cc0
    wceq
    abs00d.2
    wph
    cA
    abscld.1
    abs00ad
    mpbid
end
