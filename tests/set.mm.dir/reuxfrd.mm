include "wreu.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "reurex.mm"
include "syl.mm"
include "biantrurd.mm"
include "r19.41v.mm"
include "pm5.32i.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "reubidva.mm"
include "wrmo.mm"
include "reurmo.mm"
include "reuxfr2d.mm"
include "bitrd.mm"

theorem reuxfrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reuxfrd.1: |- ( ( ph /\ y e. B ) -> A e. B )
  assume reuxfrd.2: |- ( ( ph /\ x e. B ) -> E! y e. B x = A )
  assume reuxfrd.3: |- ( x = A -> ( ps <-> ch ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint A x
  disjoint B x
  disjoint B y
  assert |- ( ph -> ( E! x e. B ps <-> E! y e. B ch ) )

  proof
    wph
    wps
    vx
    cB
    wreu
    vx
    cv
    #
    cA
    wceq
    #
    wch
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wreu
    wch
    vy
    cB
    wreu
    wph
    wps
    @3
    vx
    cB
    wph
    @0
    cB
    wcel
    wa
    #
    wps
    @1
    vy
    cB
    wrex
    #
    wps
    wa
    #
    @3
    @4
    @5
    wps
    @4
    @1
    vy
    cB
    wreu
    #
    @5
    reuxfrd.2
    @1
    vy
    cB
    reurex
    syl
    biantrurd
    @6
    @1
    wps
    wa
    #
    vy
    cB
    wrex
    @3
    @1
    wps
    vy
    cB
    r19.41v
    @8
    @2
    vy
    cB
    @1
    wps
    wch
    reuxfrd.3
    pm5.32i
    rexbii
    bitr3i
    syl6bb
    reubidva
    wph
    wch
    vx
    vy
    cA
    cB
    reuxfrd.1
    @4
    @7
    @1
    vy
    cB
    wrmo
    reuxfrd.2
    @1
    vy
    cB
    reurmo
    syl
    reuxfr2d
    bitrd
end
