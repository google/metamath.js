include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "isseti.mm"
include "biimpd.mm"
include "eximii.mm"
include "19.36i.mm"
include "mpg.mm"

theorem vtoclf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume vtoclf.1: |- F/ x ps
  assume vtoclf.2: |- A e. _V
  assume vtoclf.3: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclf.4: |- ph

  disjoint A x
  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    vtoclf.1
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
    vtoclf.2
    isseti
    @0
    wph
    wps
    vtoclf.3
    biimpd
    eximii
    19.36i
    vtoclf.4
    mpg
end
