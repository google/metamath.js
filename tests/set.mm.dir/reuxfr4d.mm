include "wreu.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "reurex.mm"
include "syl.mm"
include "biantrurd.mm"
include "wb.mm"
include "r19.41v.mm"
include "pm5.32da.mm"
include "rexbidv.mm"
include "syl5bbr.mm"
include "adantr.mm"
include "bitrd.mm"
include "reubidva.mm"
include "wrmo.mm"
include "reurmo.mm"
include "reuxfr3d.mm"

theorem reuxfr4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume reuxfr4d.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume reuxfr4d.2: |- ( ( ph /\ x e. B ) -> E! y e. C x = A )
  assume reuxfr4d.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint A x
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( E! x e. B ps <-> E! y e. C ch ) )

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
    cC
    wrex
    #
    vx
    cB
    wreu
    wch
    vy
    cC
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
    #
    wa
    #
    wps
    @1
    vy
    cC
    wrex
    #
    wps
    wa
    #
    @3
    @5
    @6
    wps
    @5
    @1
    vy
    cC
    wreu
    #
    @6
    reuxfr4d.2
    @1
    vy
    cC
    reurex
    syl
    biantrurd
    wph
    @7
    @3
    wb
    @4
    @7
    @1
    wps
    wa
    #
    vy
    cC
    wrex
    wph
    @3
    @1
    wps
    vy
    cC
    r19.41v
    wph
    @9
    @2
    vy
    cC
    wph
    @1
    wps
    wch
    reuxfr4d.3
    pm5.32da
    rexbidv
    syl5bbr
    adantr
    bitrd
    reubidva
    wph
    wch
    vx
    vy
    cA
    cB
    cC
    reuxfr4d.1
    @5
    @8
    @1
    vy
    cC
    wrmo
    reuxfr4d.2
    @1
    vy
    cC
    reurmo
    syl
    reuxfr3d
    bitrd
end
