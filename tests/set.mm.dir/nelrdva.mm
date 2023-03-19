include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqidd.mm"
include "wne.mm"
include "cv.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "neeq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "neneqd.mm"
include "pm2.65da.mm"

theorem nelrdva
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nelrdva.1: |- ( ( ph /\ x e. A ) -> x =/= B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> -. B e. A )

  proof
    wph
    cB
    cA
    wcel
    #
    cB
    cB
    wceq
    wph
    @0
    wa
    #
    cB
    eqidd
    @1
    cB
    cB
    wph
    @0
    cB
    cB
    wne
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @3
    cB
    wne
    #
    wi
    @1
    @2
    wi
    vx
    cB
    cA
    @3
    cB
    wceq
    #
    @5
    @1
    @6
    @2
    @7
    @4
    @0
    wph
    @3
    cB
    cA
    eleq1
    anbi2d
    @3
    cB
    cB
    neeq1
    imbi12d
    nelrdva.1
    vtoclg
    anabsi7
    neneqd
    pm2.65da
end
