include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "sseq2.mm"
include "adantl.mm"
include "eqeq2.mm"
include "syl6bir.mm"
include "imp.mm"
include "imbi12d.mm"
include "wn.mm"
include "imbi1d.mm"
include "ss0.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "pm5.74d.mm"
include "sylan9bbr.mm"
include "pm2.61ian.mm"
include "imbi2d.mm"
include "a1d.mm"
include "wex.mm"
include "vex.mm"
include "sucex.mm"
include "eqvinc.mm"
include "syl5ibr.mm"
include "biimpd.mm"
include "sylan9r.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "imim2i.mm"
include "com4r.mm"
include "wne.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "annim.mm"
include "bitri.mm"
include "onsssuc.mm"
include "suceloni.mm"
include "onelpss.mm"
include "sylan2.mm"
include "bitrd.mm"
include "ancoms.mm"
include "ex.mm"
include "ax-1.mm"
include "syl8.mm"
include "a2d.mm"
include "com23.mm"
include "sylbird.mm"
include "syl5bir.mm"
include "pm2.61d.mm"
include "wlim.mm"
include "wral.mm"
include "pm2.27.mm"
include "ralimdv.mm"
include "ad2antlr.mm"
include "syld.mm"
include "exp31.mm"
include "com3l.mm"
include "com4t.mm"
include "tfinds.mm"
include "imp31.mm"

theorem tfindsg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume tfindsg.1: |- ( x = B -> ( ph <-> ps ) )
  assume tfindsg.2: |- ( x = y -> ( ph <-> ch ) )
  assume tfindsg.3: |- ( x = suc y -> ( ph <-> th ) )
  assume tfindsg.4: |- ( x = A -> ( ph <-> ta ) )
  assume tfindsg.5: |- ( B e. On -> ps )
  assume tfindsg.6: |- ( ( ( y e. On /\ B e. On ) /\ B C_ y ) -> ( ch -> th ) )
  assume tfindsg.7: |- ( ( ( Lim x /\ B e. On ) /\ B C_ x ) -> ( A. y e. x ( B C_ y -> ch ) -> ph ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( ( ( A e. On /\ B e. On ) /\ B C_ A ) -> ta )

  proof
    cA
    con0
    wcel
    cB
    con0
    wcel
    #
    cB
    cA
    wss
    #
    wta
    @0
    cB
    vx
    cv
    #
    wss
    #
    wph
    wi
    #
    wi
    @0
    cB
    c0
    wss
    #
    wps
    wi
    #
    wi
    @0
    cB
    vy
    cv
    #
    wss
    #
    wch
    wi
    #
    wi
    #
    @0
    cB
    @7
    csuc
    #
    wss
    #
    wth
    wi
    #
    wi
    @0
    @1
    wta
    wi
    #
    wi
    vx
    vy
    cA
    @2
    c0
    wceq
    #
    @4
    @6
    @0
    cB
    c0
    wceq
    #
    @15
    @4
    @6
    wb
    @16
    @15
    wa
    @3
    @5
    wph
    wps
    @15
    @3
    @5
    wb
    @16
    @2
    c0
    cB
    sseq2
    #
    adantl
    @16
    @15
    wph
    wps
    wb
    #
    @16
    @15
    @2
    cB
    wceq
    #
    @18
    cB
    c0
    @2
    eqeq2
    tfindsg.1
    syl6bir
    imp
    imbi12d
    @15
    @4
    @5
    wph
    wi
    @16
    wn
    #
    @6
    @15
    @3
    @5
    wph
    @17
    imbi1d
    @20
    @5
    wph
    wps
    @20
    @5
    @18
    @5
    @16
    cB
    ss0
    con3i
    pm2.21d
    pm5.74d
    sylan9bbr
    pm2.61ian
    imbi2d
    @2
    @7
    wceq
    #
    @4
    @9
    @0
    @21
    @3
    @8
    wph
    wch
    @2
    @7
    cB
    sseq2
    tfindsg.2
    imbi12d
    imbi2d
    @2
    @11
    wceq
    #
    @4
    @13
    @0
    @22
    @3
    @12
    wph
    wth
    @2
    @11
    cB
    sseq2
    tfindsg.3
    imbi12d
    imbi2d
    @2
    cA
    wceq
    #
    @4
    @14
    @0
    @23
    @3
    @1
    wph
    wta
    @2
    cA
    cB
    sseq2
    tfindsg.4
    imbi12d
    imbi2d
    @0
    wps
    @5
    tfindsg.5
    a1d
    @7
    con0
    wcel
    #
    @0
    @9
    @13
    @24
    @0
    @9
    @13
    wi
    #
    @24
    @0
    wa
    #
    @12
    cB
    @11
    wceq
    #
    wi
    #
    @25
    @0
    @28
    @25
    wi
    @24
    @28
    @9
    @12
    @0
    wth
    @28
    @12
    @0
    wth
    wi
    #
    wi
    @9
    @27
    @29
    @12
    @29
    @11
    cB
    @11
    cB
    wceq
    @22
    @19
    wa
    #
    vx
    wex
    @29
    vx
    @11
    cB
    @7
    vy
    vex
    sucex
    eqvinc
    @30
    @29
    vx
    @19
    @0
    wph
    @22
    wth
    @0
    wph
    @19
    wps
    tfindsg.5
    tfindsg.1
    syl5ibr
    @22
    wph
    wth
    tfindsg.3
    biimpd
    sylan9r
    exlimiv
    sylbi
    eqcoms
    imim2i
    a1d
    com4r
    adantl
    @28
    wn
    #
    @12
    cB
    @11
    wne
    #
    wa
    #
    @26
    @25
    @33
    @12
    @27
    wn
    #
    wa
    @31
    @32
    @34
    @12
    cB
    @11
    df-ne
    anbi2i
    @12
    @27
    annim
    bitri
    @26
    @33
    @8
    @25
    @0
    @24
    @8
    @33
    wb
    @0
    @24
    wa
    @8
    cB
    @11
    wcel
    #
    @33
    cB
    @7
    onsssuc
    @24
    @0
    @11
    con0
    wcel
    @35
    @33
    wb
    @7
    suceloni
    cB
    @11
    onelpss
    sylan2
    bitrd
    ancoms
    @26
    @9
    @8
    @13
    @26
    @8
    wch
    @13
    @26
    @8
    wch
    wth
    @13
    @26
    @8
    wch
    wth
    wi
    tfindsg.6
    ex
    wth
    @12
    ax-1
    syl8
    a2d
    com23
    sylbird
    syl5bir
    pm2.61d
    ex
    a2d
    @0
    @3
    @2
    wlim
    #
    @10
    vy
    @2
    wral
    #
    wph
    @36
    @0
    @3
    @37
    wph
    wi
    #
    @36
    @0
    @3
    @38
    @36
    @0
    wa
    @3
    wa
    @37
    @9
    vy
    @2
    wral
    #
    wph
    @0
    @37
    @39
    wi
    @36
    @3
    @0
    @10
    @9
    vy
    @2
    @0
    @9
    pm2.27
    ralimdv
    ad2antlr
    tfindsg.7
    syld
    exp31
    com3l
    com4t
    tfinds
    imp31
end
