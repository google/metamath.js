include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "pm5.32da.mm"
include "exbid.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem rexbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexbida.1: |- F/ x ph
  assume rexbida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wex
    @0
    wch
    wa
    #
    vx
    wex
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    wph
    @1
    @2
    vx
    rexbida.1
    wph
    @0
    wps
    wch
    rexbida.2
    pm5.32da
    exbid
    wps
    vx
    cA
    df-rex
    wch
    vx
    cA
    df-rex
    3bitr4g
end
