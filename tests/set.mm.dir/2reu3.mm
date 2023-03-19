include "wrmo.mm"
include "wo.mm"
include "wral.mm"
include "wreu.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "orcom.mm"
include "ralbii.mm"
include "nfrmo1.mm"
include "r19.32.mm"
include "bitri.mm"
include "nfcv.mm"
include "nfral.mm"
include "wi.mm"
include "2reu1.mm"
include "biimpd.mm"
include "ancom.mm"
include "syl6ib.mm"
include "adantld.mm"
include "adantrd.mm"
include "jaoi.mm"
include "2rexreu.mm"
include "ancoms.mm"
include "jca.mm"
include "impbid1.mm"
include "sylbi.mm"

theorem 2reu3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( A. x e. A A. y e. B ( E* x e. A ph \/ E* y e. B ph ) -> ( ( E! x e. A E! y e. B ph /\ E! y e. B E! x e. A ph ) <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) )

  proof
    wph
    vx
    cA
    wrmo
    #
    wph
    vy
    cB
    wrmo
    #
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
    @0
    vy
    cB
    wral
    #
    @1
    vx
    cA
    wral
    #
    wo
    #
    wph
    vy
    cB
    wreu
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wreu
    vy
    cB
    wreu
    #
    wa
    #
    wph
    vy
    cB
    wrex
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    vy
    cB
    wreu
    #
    wa
    #
    wb
    @4
    @5
    @1
    wo
    #
    vx
    cA
    wral
    @7
    @3
    @14
    vx
    cA
    @3
    @1
    @5
    wo
    #
    @14
    @3
    @1
    @0
    wo
    #
    vy
    cB
    wral
    @15
    @2
    @16
    vy
    cB
    @0
    @1
    orcom
    ralbii
    @1
    @0
    vy
    cB
    wph
    vy
    cB
    nfrmo1
    r19.32
    bitri
    @1
    @5
    orcom
    bitri
    ralbii
    @5
    @1
    vx
    cA
    @0
    vx
    vy
    cB
    vx
    cB
    nfcv
    wph
    vx
    cA
    nfrmo1
    nfral
    r19.32
    bitri
    @7
    @10
    @13
    @5
    @10
    @13
    wi
    @6
    @5
    @9
    @13
    @8
    @5
    @9
    @12
    @11
    wa
    #
    @13
    @5
    @9
    @17
    wph
    vy
    vx
    cB
    cA
    2reu1
    biimpd
    @12
    @11
    ancom
    syl6ib
    adantld
    @6
    @8
    @13
    @9
    @6
    @8
    @13
    wph
    vx
    vy
    cA
    cB
    2reu1
    biimpd
    adantrd
    jaoi
    @13
    @8
    @9
    wph
    vx
    vy
    cA
    cB
    2rexreu
    @12
    @11
    @9
    wph
    vy
    vx
    cB
    cA
    2rexreu
    ancoms
    jca
    impbid1
    sylbi
end
