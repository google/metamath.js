include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "con3d.mm"
include "rspcimdv.mm"
include "con2d.mm"
include "dfrex2.mm"
include "syl6ibr.mm"

theorem rspcimedv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcimdv.1: |- ( ph -> A e. B )
  assume rspcimedv.2: |- ( ( ph /\ x = A ) -> ( ch -> ps ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( ch -> E. x e. B ps ) )

  proof
    wph
    wch
    wps
    wn
    #
    vx
    cB
    wral
    #
    wn
    wps
    vx
    cB
    wrex
    wph
    @1
    wch
    wph
    @0
    wch
    wn
    vx
    cA
    cB
    rspcimdv.1
    wph
    vx
    cv
    cA
    wceq
    wa
    wch
    wps
    rspcimedv.2
    con3d
    rspcimdv
    con2d
    wps
    vx
    cB
    dfrex2
    syl6ibr
end
