include "cmoore.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "selpw.mm"
include "wn.mm"
include "pm2.1.mm"
include "biantru.mm"
include "andi.mm"
include "bitri.mm"
include "df-ne.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "simpr.mm"
include "id.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "ancri.mm"
include "impbii.mm"
include "orbi12i.mm"
include "expl.mm"
include "wi.mm"
include "intssuni2.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "syl.mm"
include "sylcom.mm"
include "rint0.mm"
include "syl5ibcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wb.mm"
include "bj-ismoore.mm"
include "mpbird.mm"

theorem bj-ismooredr2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-ismooredr2.1: |- ( ph -> A e. V )
  assume bj-ismooredr2.2: |- ( ph -> U. A e. A )
  assume bj-ismooredr2.3: |- ( ( ( ph /\ x C_ A ) /\ x =/= (/) ) -> |^| x e. A )

  disjoint ph x
  disjoint A x
  assert |- ( ph -> A e. Moore_ )

  proof
    wph
    cA
    cmoore
    wcel
    #
    cA
    cuni
    #
    vx
    cv
    #
    cint
    #
    cin
    #
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    #
    wph
    @5
    vx
    @6
    @2
    @6
    wcel
    #
    @2
    cA
    wss
    #
    @2
    c0
    wne
    #
    wa
    #
    @2
    c0
    wceq
    #
    wo
    #
    wph
    @5
    @8
    @9
    @13
    vx
    cA
    selpw
    @9
    @9
    @12
    wn
    #
    wa
    #
    @9
    @12
    wa
    #
    wo
    #
    @13
    @9
    @9
    @14
    @12
    wo
    #
    wa
    @17
    @18
    @9
    @12
    pm2.1
    biantru
    @9
    @14
    @12
    andi
    bitri
    @15
    @11
    @16
    @12
    @14
    @10
    @9
    @10
    @14
    @2
    c0
    df-ne
    bicomi
    anbi2i
    @16
    @12
    @9
    @12
    simpr
    @12
    @9
    @12
    @2
    c0
    cA
    @12
    id
    cA
    0ss
    syl6eqss
    ancri
    impbii
    orbi12i
    bitri
    bitri
    wph
    @11
    @5
    @12
    wph
    @11
    @3
    cA
    wcel
    #
    @5
    wph
    @9
    @10
    @19
    bj-ismooredr2.3
    expl
    @11
    @3
    @1
    wss
    #
    @19
    @5
    wi
    @2
    cA
    intssuni2
    @20
    @19
    @5
    @20
    @3
    @4
    cA
    @20
    @4
    @3
    @20
    @4
    @3
    wceq
    @3
    @1
    sseqin2
    biimpi
    eqcomd
    eleq1d
    biimpd
    syl
    sylcom
    wph
    @1
    cA
    wcel
    @12
    @5
    bj-ismooredr2.2
    @12
    @1
    @4
    cA
    @12
    @4
    @1
    @1
    @2
    rint0
    eqcomd
    eleq1d
    syl5ibcom
    jaod
    syl5bi
    ralrimiv
    wph
    cA
    cV
    wcel
    @0
    @7
    wb
    bj-ismooredr2.1
    vx
    cA
    cV
    bj-ismoore
    syl
    mpbird
end
