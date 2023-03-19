include "wrex.mm"
include "wa.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "cv.mm"
include "wcel.mm"
include "adantllr.mm"
include "simpr.mm"
include "r19.29af.mm"

theorem r19.29an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume r19.29an.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )

  disjoint ch x
  disjoint ph x
  assert |- ( ( ph /\ E. x e. A ps ) -> ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    #
    wa
    wps
    wch
    vx
    cA
    wph
    @0
    vx
    wph
    vx
    nfv
    wps
    vx
    cA
    nfre1
    nfan
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    @0
    r19.29an.1
    adantllr
    wph
    @0
    simpr
    r19.29af
end
