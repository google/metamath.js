include "cif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cab.mm"
include "wi.mm"
include "df-if.mm"
include "df-or.mm"
include "orcom.mm"
include "iman.mm"
include "imbi1i.mm"
include "3bitr4i.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfif2
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B
  let cC: class C

  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint C x
  assert |- if ( ph , A , B ) = { x | ( ( x e. B -> ph ) -> ( x e. A /\ ph ) ) }

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
    wph
    wa
    #
    @0
    cB
    wcel
    #
    wph
    wn
    wa
    #
    wo
    #
    vx
    cab
    @2
    wph
    wi
    #
    @1
    wi
    #
    vx
    cab
    wph
    vx
    cA
    cB
    df-if
    @4
    @6
    vx
    @3
    @1
    wo
    @3
    wn
    #
    @1
    wi
    @4
    @6
    @3
    @1
    df-or
    @1
    @3
    orcom
    @5
    @7
    @1
    @2
    wph
    iman
    imbi1i
    3bitr4i
    abbii
    eqtri
end
