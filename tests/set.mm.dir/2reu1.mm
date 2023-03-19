include "wrmo.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "2reu5a.mm"
include "cv.mm"
include "wcel.mm"
include "simprr.mm"
include "rsp.mm"
include "adantr.mm"
include "impcom.mm"
include "jca.mm"
include "ex.mm"
include "rmoimia.mm"
include "nfra1.mm"
include "rmoanim.mm"
include "sylib.mm"
include "ancrd.mm"
include "2rmoswap.mm"
include "com12.mm"
include "imdistani.mm"
include "syl6.mm"
include "simplbiim.mm"
include "2reu2rex.mm"
include "rexcom.mm"
include "jctild.mm"
include "reu5.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "2rexreu.mm"
include "impbid1.mm"

theorem 2reu1
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
  disjoint k x
  assert |- ( A. x e. A E* y e. B ph -> ( E! x e. A E! y e. B ph <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) )

  proof
    wph
    vy
    cB
    wrmo
    #
    vx
    cA
    wral
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
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wa
    #
    @2
    @1
    @7
    @2
    @1
    @3
    vx
    cA
    wrex
    #
    @5
    vy
    cB
    wrex
    #
    wa
    #
    @3
    vx
    cA
    wrmo
    #
    @5
    vy
    cB
    wrmo
    #
    wa
    #
    wa
    #
    @7
    @2
    @1
    @13
    @10
    @2
    @3
    @0
    wa
    #
    vx
    cA
    wrex
    @15
    vx
    cA
    wrmo
    #
    @1
    @13
    wi
    wph
    vx
    vy
    cA
    cB
    2reu5a
    @16
    @1
    @11
    @1
    wa
    @13
    @16
    @1
    @11
    @16
    @1
    @3
    wa
    #
    vx
    cA
    wrmo
    @1
    @11
    wi
    @17
    @15
    vx
    cA
    vx
    cv
    cA
    wcel
    #
    @17
    @15
    @18
    @17
    wa
    @3
    @0
    @18
    @1
    @3
    simprr
    @17
    @18
    @0
    @1
    @18
    @0
    wi
    @3
    @0
    vx
    cA
    rsp
    adantr
    impcom
    jca
    ex
    rmoimia
    @1
    @3
    vx
    cA
    @0
    vx
    cA
    nfra1
    rmoanim
    sylib
    ancrd
    @11
    @1
    @12
    @1
    @11
    @12
    wph
    vx
    vy
    cA
    cB
    2rmoswap
    com12
    imdistani
    syl6
    simplbiim
    @2
    @8
    @9
    wph
    vx
    vy
    cA
    cB
    2reu2rex
    #
    @2
    @8
    @9
    @19
    wph
    vx
    vy
    cA
    cB
    rexcom
    sylib
    jca
    jctild
    @7
    @8
    @11
    wa
    #
    @9
    @12
    wa
    #
    wa
    @14
    @4
    @20
    @6
    @21
    @3
    vx
    cA
    reu5
    @5
    vy
    cB
    reu5
    anbi12i
    @8
    @11
    @9
    @12
    an4
    bitri
    syl6ibr
    com12
    wph
    vx
    vy
    cA
    cB
    2rexreu
    impbid1
end
