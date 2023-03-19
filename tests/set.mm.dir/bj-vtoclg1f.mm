include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-elisset.mm"
include "bj-exlimmpi.mm"
include "syl.mm"

theorem bj-vtoclg1f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-vtoclg1f.nf: |- F/ x ps
  assume bj-vtoclg1f.maj: |- ( x = A -> ( ph -> ps ) )
  assume bj-vtoclg1f.min: |- ph

  disjoint A x
  assert |- ( A e. V -> ps )

  proof
    cA
    cV
    wcel
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    wps
    vx
    cA
    cV
    bj-elisset
    wph
    wps
    @0
    vx
    bj-vtoclg1f.nf
    bj-vtoclg1f.maj
    bj-vtoclg1f.min
    bj-exlimmpi
    syl
end
