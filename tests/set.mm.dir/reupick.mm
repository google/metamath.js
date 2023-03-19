include "wss.mm"
include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "ssel.mm"
include "ad2antrr.mm"
include "wex.mm"
include "weu.mm"
include "df-rex.mm"
include "df-reu.mm"
include "anbi12i.mm"
include "ancrd.mm"
include "anim1d.mm"
include "an32.mm"
include "syl6ib.mm"
include "eximdv.mm"
include "eupick.mm"
include "ex.mm"
include "syl9.mm"
include "com23.mm"
include "imp32.mm"
include "sylan2b.mm"
include "expcomd.mm"
include "imp.mm"
include "impbid.mm"

theorem reupick
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ( A C_ B /\ ( E. x e. A ph /\ E! x e. B ph ) ) /\ ph ) -> ( x e. A <-> x e. B ) )

  proof
    cA
    cB
    wss
    #
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cB
    wreu
    #
    wa
    #
    wa
    #
    wph
    wa
    vx
    cv
    #
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    @0
    @6
    @7
    wi
    @3
    wph
    cA
    cB
    @5
    ssel
    #
    ad2antrr
    @4
    wph
    @7
    @6
    wi
    @4
    @7
    wph
    @6
    @3
    @0
    @6
    wph
    wa
    #
    vx
    wex
    #
    @7
    wph
    wa
    #
    vx
    weu
    #
    wa
    @11
    @6
    wi
    #
    @1
    @10
    @2
    @12
    wph
    vx
    cA
    df-rex
    wph
    vx
    cB
    df-reu
    anbi12i
    @0
    @10
    @12
    @13
    @0
    @12
    @10
    @13
    @0
    @10
    @11
    @6
    wa
    #
    vx
    wex
    #
    @12
    @13
    @0
    @9
    @14
    vx
    @0
    @9
    @7
    @6
    wa
    #
    wph
    wa
    @14
    @0
    @6
    @16
    wph
    @0
    @6
    @7
    @8
    ancrd
    anim1d
    @7
    @6
    wph
    an32
    syl6ib
    eximdv
    @12
    @15
    @13
    @11
    @6
    vx
    eupick
    ex
    syl9
    com23
    imp32
    sylan2b
    expcomd
    imp
    impbid
end
