include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"

theorem ralss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> ( A. x e. A ph <-> A. x e. B ( x e. A -> ph ) ) )

  proof
    cA
    cB
    wss
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wi
    #
    vx
    cA
    cB
    @0
    @3
    @1
    cB
    wcel
    #
    @2
    wa
    #
    wph
    wi
    @4
    @3
    wi
    @0
    @2
    @5
    wph
    @0
    @2
    @4
    cA
    cB
    @1
    ssel
    pm4.71rd
    imbi1d
    @4
    @2
    wph
    impexp
    syl6bb
    ralbidv2
end
