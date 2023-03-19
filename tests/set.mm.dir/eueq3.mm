include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "w3o.mm"
include "weu.mm"
include "eueq1.mm"
include "ibar.mm"
include "wb.mm"
include "pm2.45.mm"
include "imnani.mm"
include "con2i.mm"
include "jaoi.mm"
include "bianfd.mm"
include "orbi12d.mm"
include "mtbid.mm"
include "biorf.mm"
include "syl.mm"
include "bitrd.mm"
include "3orrot.mm"
include "df-3or.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "eubidv.mm"
include "mpbii.mm"
include "adantr.mm"
include "pm2.46.mm"
include "simpl.mm"
include "orim12i.mm"
include "con3i.mm"
include "3orcomb.mm"
include "ecase3.mm"

theorem eueq3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume eueq3.1: |- A e. _V
  assume eueq3.2: |- B e. _V
  assume eueq3.3: |- C e. _V
  assume eueq3.4: |- -. ( ph /\ ps )

  disjoint ph x
  disjoint ps x
  disjoint A x
  disjoint B x
  disjoint C x
  assert |- E! x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) )

  proof
    wph
    wps
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wa
    #
    wph
    wps
    wo
    #
    wn
    #
    @0
    cB
    wceq
    #
    wa
    #
    wps
    @0
    cC
    wceq
    #
    wa
    #
    w3o
    #
    vx
    weu
    #
    wph
    @1
    vx
    weu
    @10
    vx
    cA
    eueq3.1
    eueq1
    wph
    @1
    @9
    vx
    wph
    @1
    @6
    @8
    wo
    #
    @2
    wo
    #
    @9
    wph
    @1
    @2
    @12
    wph
    @1
    ibar
    wph
    @11
    wn
    @2
    @12
    wb
    wph
    @4
    wps
    wo
    #
    @11
    @13
    wph
    @4
    wph
    wn
    wps
    wph
    wps
    pm2.45
    #
    wph
    wps
    wph
    wps
    eueq3.4
    imnani
    #
    con2i
    jaoi
    con2i
    wph
    @4
    @6
    wps
    @8
    wph
    @4
    @5
    @4
    wph
    @14
    con2i
    bianfd
    wph
    wps
    @7
    @15
    bianfd
    orbi12d
    mtbid
    @11
    @2
    biorf
    syl
    bitrd
    @9
    @6
    @8
    @2
    w3o
    @12
    @2
    @6
    @8
    3orrot
    @6
    @8
    @2
    df-3or
    bitri
    syl6bbr
    eubidv
    mpbii
    wps
    @7
    vx
    weu
    @10
    vx
    cC
    eueq3.3
    eueq1
    wps
    @7
    @9
    vx
    wps
    @7
    @2
    @6
    wo
    #
    @8
    wo
    #
    @9
    wps
    @7
    @8
    @17
    wps
    @7
    ibar
    wps
    @16
    wn
    @8
    @17
    wb
    @16
    wps
    @2
    wps
    wn
    #
    @6
    wph
    @18
    @1
    @15
    adantr
    @4
    @18
    @5
    wph
    wps
    pm2.46
    adantr
    jaoi
    con2i
    @16
    @8
    biorf
    syl
    bitrd
    @2
    @6
    @8
    df-3or
    syl6bbr
    eubidv
    mpbii
    @4
    @5
    vx
    weu
    @10
    vx
    cB
    eueq3.2
    eueq1
    @4
    @5
    @9
    vx
    @4
    @5
    @2
    @8
    wo
    #
    @6
    wo
    #
    @9
    @4
    @5
    @6
    @20
    @4
    @5
    ibar
    @4
    @19
    wn
    @6
    @20
    wb
    @19
    @3
    @2
    wph
    @8
    wps
    wph
    @1
    simpl
    wps
    @7
    simpl
    orim12i
    con3i
    @19
    @6
    biorf
    syl
    bitrd
    @9
    @2
    @8
    @6
    w3o
    @20
    @2
    @6
    @8
    3orcomb
    @2
    @8
    @6
    df-3or
    bitri
    syl6bbr
    eubidv
    mpbii
    ecase3
end
