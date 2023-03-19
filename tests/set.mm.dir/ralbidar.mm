include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wb.mm"
include "ex.mm"
include "ralimi.mm"
include "syl.mm"
include "df-ral.mm"
include "sylib.mm"
include "pm2.43.mm"
include "pm5.74d.mm"
include "alimi.mm"
include "albi.mm"
include "3syl.mm"
include "3bitr4g.mm"

theorem ralbidar
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbidar.1: |- ( ph -> A. x e. A ph )
  assume ralbidar.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wi
    #
    vx
    wal
    #
    @0
    wch
    wi
    #
    vx
    wal
    #
    wps
    vx
    cA
    wral
    wch
    vx
    cA
    wral
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
    pm5.74d
    alimi
    @1
    @3
    vx
    albi
    3syl
    wps
    vx
    cA
    df-ral
    wch
    vx
    cA
    df-ral
    3bitr4g
end
