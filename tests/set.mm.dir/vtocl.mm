include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "isseti.mm"
include "biimpd.mm"
include "eximii.mm"
include "19.36iv.mm"
include "mpg.mm"

theorem vtocl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume vtocl.1: |- A e. _V
  assume vtocl.2: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl.3: |- ph

  disjoint A x
  disjoint ps x
  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wi
    vx
    vx
    cA
    vtocl.1
    isseti
    @0
    wph
    wps
    vtocl.2
    biimpd
    eximii
    19.36iv
    vtocl.3
    mpg
end
