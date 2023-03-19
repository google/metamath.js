include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wrex.mm"
include "wceq.mm"
include "wreu.mm"
include "reurex.mm"
include "syl.mm"
include "rexxfrd.mm"
include "df-rex.mm"
include "3bitr3g.mm"
include "reuxfr4d.mm"
include "df-reu.mm"
include "imbi12d.mm"
include "df-mo.mm"
include "3bitr4g.mm"
include "df-rmo.mm"

theorem rmoxfrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume rmoxfrd.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume rmoxfrd.2: |- ( ( ph /\ x e. B ) -> E! y e. C x = A )
  assume rmoxfrd.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  assert |- ( ph -> ( E* x e. B ps <-> E* y e. C ch ) )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wps
    wa
    #
    vx
    wmo
    #
    vy
    cv
    cC
    wcel
    wch
    wa
    #
    vy
    wmo
    #
    wps
    vx
    cB
    wrmo
    wch
    vy
    cC
    wrmo
    wph
    @2
    vx
    wex
    #
    @2
    vx
    weu
    #
    wi
    @4
    vy
    wex
    #
    @4
    vy
    weu
    #
    wi
    @3
    @5
    wph
    @6
    @8
    @7
    @9
    wph
    wps
    vx
    cB
    wrex
    wch
    vy
    cC
    wrex
    @6
    @8
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    rmoxfrd.1
    wph
    @1
    wa
    @0
    cA
    wceq
    #
    vy
    cC
    wreu
    @10
    vy
    cC
    wrex
    rmoxfrd.2
    @10
    vy
    cC
    reurex
    syl
    rmoxfrd.3
    rexxfrd
    wps
    vx
    cB
    df-rex
    wch
    vy
    cC
    df-rex
    3bitr3g
    wph
    wps
    vx
    cB
    wreu
    wch
    vy
    cC
    wreu
    @7
    @9
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    rmoxfrd.1
    rmoxfrd.2
    rmoxfrd.3
    reuxfr4d
    wps
    vx
    cB
    df-reu
    wch
    vy
    cC
    df-reu
    3bitr3g
    imbi12d
    @2
    vx
    df-mo
    @4
    vy
    df-mo
    3bitr4g
    wps
    vx
    cB
    df-rmo
    wch
    vy
    cC
    df-rmo
    3bitr4g
end
