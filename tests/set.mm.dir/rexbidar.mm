include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "ex.mm"
include "ralimi.mm"
include "syl.mm"
include "df-ral.mm"
include "sylib.mm"
include "pm2.43.mm"
include "pm5.32d.mm"
include "alimi.mm"
include "exbi.mm"
include "3syl.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem rexbidar
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbidar.1: |- ( ph -> A. x e. A ph )
  assume ralbidar.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


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
    #
    @0
    wch
    wa
    #
    vx
    wex
    #
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    wph
    @0
    @0
    wps
    wch
    wb
    #
    wi
    #
    wi
    #
    vx
    wal
    #
    @1
    @3
    wb
    #
    vx
    wal
    @2
    @4
    wb
    wph
    @6
    vx
    cA
    wral
    #
    @8
    wph
    wph
    vx
    cA
    wral
    @10
    ralbidar.1
    wph
    @6
    vx
    cA
    wph
    @0
    @5
    ralbidar.2
    ex
    ralimi
    syl
    @6
    vx
    cA
    df-ral
    sylib
    @7
    @9
    vx
    @7
    @0
    wps
    wch
    @0
    @5
    pm2.43
    pm5.32d
    alimi
    @1
    @3
    vx
    exbi
    3syl
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
