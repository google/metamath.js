include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "bj-issetiv.mm"
include "biimpd.mm"
include "eximii.mm"
include "19.36i.mm"
include "mpg.mm"

theorem bj-vtoclf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-vtoclf.nf: |- F/ x ps
  assume bj-vtoclf.s: |- A e. V
  assume bj-vtoclf.maj: |- ( x = A -> ( ph <-> ps ) )
  assume bj-vtoclf.min: |- ph

  disjoint A x
  disjoint V x
  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    bj-vtoclf.nf
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
    cV
    bj-vtoclf.s
    bj-issetiv
    @0
    wph
    wps
    bj-vtoclf.maj
    biimpd
    eximii
    19.36i
    bj-vtoclf.min
    mpg
end
