include "wo.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wa.mm"
include "rexnal.mm"
include "anbi12i.mm"
include "ioran.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "reeanv.mm"
include "3bitr3ri.mm"
include "3bitr4i.mm"
include "con4bii.mm"

theorem 2ralor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint ph y
  disjoint ps x
  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( A. x e. A A. y e. B ( ph \/ ps ) <-> ( A. x e. A ph \/ A. y e. B ps ) )

  proof
    wph
    wps
    wo
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wral
    #
    wps
    vy
    cB
    wral
    #
    wo
    #
    wph
    wn
    #
    vx
    cA
    wrex
    #
    wps
    wn
    #
    vy
    cB
    wrex
    #
    wa
    #
    @3
    wn
    #
    @4
    wn
    #
    wa
    @2
    wn
    #
    @5
    wn
    @7
    @11
    @9
    @12
    wph
    vx
    cA
    rexnal
    wps
    vy
    cB
    rexnal
    anbi12i
    @6
    @8
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @1
    wn
    #
    vx
    cA
    wrex
    @10
    @13
    @15
    @16
    vx
    cA
    @15
    @0
    wn
    #
    vy
    cB
    wrex
    @16
    @17
    @14
    vy
    cB
    wph
    wps
    ioran
    rexbii
    @0
    vy
    cB
    rexnal
    bitr3i
    rexbii
    @6
    @8
    vx
    vy
    cA
    cB
    reeanv
    @1
    vx
    cA
    rexnal
    3bitr3ri
    @3
    @4
    ioran
    3bitr4i
    con4bii
end
