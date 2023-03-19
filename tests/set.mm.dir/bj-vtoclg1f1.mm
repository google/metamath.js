include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-denotes.mm"
include "bj-exlimmpi.mm"
include "sylbi.mm"

theorem bj-vtoclg1f1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume bj-vtoclg1f1.nf: |- F/ x ps
  assume bj-vtoclg1f1.maj: |- ( x = A -> ( ph -> ps ) )
  assume bj-vtoclg1f1.min: |- ph

  disjoint A x
  disjoint A y
  assert |- ( E. y y = A -> ps )

  proof
    vy
    cv
    cA
    wceq
    vy
    wex
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    wps
    vy
    vx
    cA
    bj-denotes
    wph
    wps
    @0
    vx
    bj-vtoclg1f1.nf
    bj-vtoclg1f1.maj
    bj-vtoclg1f1.min
    bj-exlimmpi
    sylbi
end
