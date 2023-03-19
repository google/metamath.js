include "cif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cab.mm"
include "wif.mm"
include "bj-dfifc2.mm"
include "df-ifp.mm"
include "bicomi.mm"
include "abbii.mm"
include "eqtri.mm"

theorem bj-df-ifc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- if ( ph , A , B ) = { x | if- ( ph , x e. A , x e. B ) }

  proof
    wph
    cA
    cB
    cif
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    wph
    wn
    @0
    cB
    wcel
    #
    wa
    wo
    #
    vx
    cab
    wph
    @1
    @2
    wif
    #
    vx
    cab
    wph
    vx
    cA
    cB
    bj-dfifc2
    @3
    @4
    vx
    @4
    @3
    wph
    @1
    @2
    df-ifp
    bicomi
    abbii
    eqtri
end
