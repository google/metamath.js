include "cr.mm"
include "wcel.mm"
include "cmpt.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "simpl.mm"
include "mpteq2dva.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "anabsi7.mm"

theorem stoweidlem4
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cT: class T
  let vk: setvar k
  assume stoweidlem4.1: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )

  disjoint t x
  disjoint B t
  disjoint B x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ( ph /\ B e. RR ) -> ( t e. T |-> B ) e. A )

  proof
    wph
    cB
    cr
    wcel
    #
    vt
    cT
    cB
    cmpt
    #
    cA
    wcel
    #
    wph
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    vt
    cT
    @3
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @0
    wa
    #
    @2
    wi
    vx
    cB
    cr
    @3
    cB
    wceq
    #
    @5
    @8
    @7
    @2
    @9
    @4
    @0
    wph
    @3
    cB
    cr
    eleq1
    anbi2d
    @9
    @6
    @1
    cA
    @9
    vt
    cT
    @3
    cB
    @9
    vt
    cv
    cT
    wcel
    simpl
    mpteq2dva
    eleq1d
    imbi12d
    stoweidlem4.1
    vtoclg
    anabsi7
end
