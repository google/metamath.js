include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "weu.mm"
include "df-rex.mm"
include "df-reu.mm"
include "anbi12i.mm"
include "wmo.mm"
include "wal.mm"
include "df-ral.mm"
include "ssel.mm"
include "pm3.2.mm"
include "imim2d.mm"
include "syl6.mm"
include "a2d.mm"
include "imp4a.mm"
include "alimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "euimmo.mm"
include "syl.mm"
include "eu5.mm"
include "simplbi2.mm"
include "syl9.mm"
include "imp32.mm"
include "sylibr.mm"

theorem reuss2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> E! x e. A ph )

  proof
    wph
    vx
    cA
    wrex
    #
    wps
    vx
    cB
    wreu
    #
    wa
    cA
    cB
    wss
    #
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wex
    #
    @6
    cB
    wcel
    #
    wps
    wa
    #
    vx
    weu
    #
    wa
    #
    wph
    vx
    cA
    wreu
    #
    @0
    @9
    @1
    @12
    wph
    vx
    cA
    df-rex
    wps
    vx
    cB
    df-reu
    anbi12i
    @5
    @13
    wa
    @8
    vx
    weu
    #
    @14
    @5
    @9
    @12
    @15
    @5
    @12
    @8
    vx
    wmo
    #
    @9
    @15
    @5
    @8
    @11
    wi
    #
    vx
    wal
    #
    @12
    @16
    wi
    @4
    @2
    @7
    @3
    wi
    #
    vx
    wal
    #
    @18
    @3
    vx
    cA
    df-ral
    @2
    @20
    @18
    @2
    @19
    @17
    vx
    @2
    @19
    @7
    wph
    @11
    @2
    @7
    @3
    wph
    @11
    wi
    #
    @2
    @7
    @10
    @3
    @21
    wi
    cA
    cB
    @6
    ssel
    @10
    wps
    @11
    wph
    @10
    wps
    pm3.2
    imim2d
    syl6
    a2d
    imp4a
    alimdv
    imp
    sylan2b
    @8
    @11
    vx
    euimmo
    syl
    @15
    @9
    @16
    @8
    vx
    eu5
    simplbi2
    syl9
    imp32
    wph
    vx
    cA
    df-reu
    sylibr
    sylan2b
end
