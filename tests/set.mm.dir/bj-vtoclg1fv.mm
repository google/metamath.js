include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-elissetv.mm"
include "bj-exlimmpi.mm"
include "syl.mm"

theorem bj-vtoclg1fv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-vtoclg1fv.nf: |- F/ x ps
  assume bj-vtoclg1fv.maj: |- ( x = A -> ( ph -> ps ) )
  assume bj-vtoclg1fv.min: |- ph

  disjoint A x
  disjoint V x
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
    bj-elissetv
    wph
    wps
    @0
    vx
    bj-vtoclg1fv.nf
    bj-vtoclg1fv.maj
    bj-vtoclg1fv.min
    bj-exlimmpi
    syl
end
