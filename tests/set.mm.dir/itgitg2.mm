include "cr.mm"
include "citg.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "itgposval.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "fveq2i.mm"
include "syl6eq.mm"

theorem itgitg2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume itgitg2.1: |- ( ( ph /\ x e. RR ) -> A e. RR )
  assume itgitg2.2: |- ( ( ph /\ x e. RR ) -> 0 <_ A )
  assume itgitg2.3: |- ( ph -> ( x e. RR |-> A ) e. L^1 )

  disjoint ph x
  assert |- ( ph -> S. RR A _d x = ( S.2 ` ( x e. RR |-> A ) ) )

  proof
    wph
    vx
    cr
    cA
    citg
    vx
    cr
    vx
    cv
    cr
    wcel
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    vx
    cr
    cA
    cmpt
    #
    citg2
    cfv
    wph
    vx
    cr
    cA
    itgitg2.1
    itgitg2.3
    itgitg2.2
    itgposval
    @2
    @3
    citg2
    vx
    cr
    @1
    cA
    @0
    cA
    cc0
    iftrue
    mpteq2ia
    fveq2i
    syl6eq
end
