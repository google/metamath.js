include "cif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cab.mm"
include "df-if.mm"
include "ancom.mm"
include "orbi12i.mm"
include "bicomi.mm"
include "abbii.mm"
include "eqtri.mm"

theorem bj-dfifc2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- if ( ph , A , B ) = { x | ( ( ph /\ x e. A ) \/ ( -. ph /\ x e. B ) ) }

  proof
    wph
    cA
    cB
    cif
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    @0
    cB
    wcel
    #
    wph
    wn
    #
    wa
    #
    wo
    #
    vx
    cab
    wph
    @1
    wa
    #
    @4
    @3
    wa
    #
    wo
    #
    vx
    cab
    wph
    vx
    cA
    cB
    df-if
    @6
    @9
    vx
    @9
    @6
    @7
    @2
    @8
    @5
    wph
    @1
    ancom
    @4
    @3
    ancom
    orbi12i
    bicomi
    abbii
    eqtri
end
