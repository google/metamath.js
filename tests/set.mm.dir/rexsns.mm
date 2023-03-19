include "cv.mm"
include "csn.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wrex.mm"
include "wsbc.mm"
include "velsn.mm"
include "anbi1i.mm"
include "exbii.mm"
include "df-rex.mm"
include "sbc5.mm"
include "3bitr4i.mm"

theorem rexsns
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let wps: wff ps

  disjoint A x
  disjoint ps x
  assert |- ( E. x e. { A } ph <-> [. A / x ]. ph )

  proof
    vx
    cv
    #
    cA
    csn
    #
    wcel
    #
    wph
    wa
    #
    vx
    wex
    @0
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    wph
    vx
    @1
    wrex
    wph
    vx
    cA
    wsbc
    @3
    @5
    vx
    @2
    @4
    wph
    vx
    cA
    velsn
    anbi1i
    exbii
    wph
    vx
    @1
    df-rex
    wph
    vx
    cA
    sbc5
    3bitr4i
end
