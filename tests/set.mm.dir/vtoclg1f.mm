include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isset.mm"
include "mpbii.mm"
include "exlimi.mm"
include "sylbi.mm"
include "syl.mm"

theorem vtoclg1f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtoclg1f.nf: |- F/ x ps
  assume vtoclg1f.maj: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclg1f.min: |- ph

  disjoint A x
  assert |- ( A e. V -> ps )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    wps
    cA
    cV
    elex
    @0
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
    isset
    @1
    wps
    vx
    vtoclg1f.nf
    @1
    wph
    wps
    vtoclg1f.min
    vtoclg1f.maj
    mpbii
    exlimi
    sylbi
    syl
end
