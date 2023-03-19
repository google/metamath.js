include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "weu.mm"
include "wreu.mm"
include "cvv.mm"
include "elexd.mm"
include "eueq.mm"
include "sylib.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "3expa.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "eubidv.mm"
include "mpbid.mm"
include "df-reu.mm"
include "sylibr.mm"

theorem reuhypd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume reuhypd.1: |- ( ( ph /\ x e. C ) -> B e. C )
  assume reuhypd.2: |- ( ( ph /\ x e. C /\ y e. C ) -> ( x = A <-> y = B ) )

  disjoint ph y
  disjoint B y
  disjoint C y
  disjoint x y
  assert |- ( ( ph /\ x e. C ) -> E! y e. C x = A )

  proof
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    #
    vy
    cv
    #
    cC
    wcel
    #
    @0
    cA
    wceq
    #
    wa
    #
    vy
    weu
    #
    @5
    vy
    cC
    wreu
    @2
    @3
    cB
    wceq
    #
    vy
    weu
    #
    @7
    @2
    cB
    cvv
    wcel
    @9
    @2
    cB
    cC
    reuhypd.1
    elexd
    vy
    cB
    eueq
    sylib
    @2
    @8
    @6
    vy
    @2
    @8
    @4
    @8
    wa
    @6
    @2
    @8
    @4
    @2
    @4
    @8
    cB
    cC
    wcel
    reuhypd.1
    @3
    cB
    cC
    eleq1
    syl5ibrcom
    pm4.71rd
    @2
    @4
    @5
    @8
    wph
    @1
    @4
    @5
    @8
    wb
    reuhypd.2
    3expa
    pm5.32da
    bitr4d
    eubidv
    mpbid
    @5
    vy
    cC
    df-reu
    sylibr
end
