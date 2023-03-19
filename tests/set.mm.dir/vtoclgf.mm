include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "issetf.mm"
include "mpbii.mm"
include "exlimi.mm"
include "sylbi.mm"
include "syl.mm"

theorem vtoclgf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtoclgf.1: |- F/_ x A
  assume vtoclgf.2: |- F/ x ps
  assume vtoclgf.3: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclgf.4: |- ph


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
    vtoclgf.1
    issetf
    @1
    wps
    vx
    vtoclgf.2
    @1
    wph
    wps
    vtoclgf.4
    vtoclgf.3
    mpbii
    exlimi
    sylbi
    syl
end
