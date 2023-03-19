include "com.mm"
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
include "con0.mm"
include "nnon.mm"
include "onsssuc.mm"
include "suceloni.mm"
include "onelpss.mm"
include "sylan2.mm"
include "bitrd.mm"
include "syl2anr.mm"
include "ex.mm"
include "ax-1.mm"
include "syl8.mm"
include "a2d.mm"
include "com23.mm"
include "sylbird.mm"
include "syl5bir.mm"
include "pm2.61d.mm"
include "finds.mm"
include "imp31.mm"

theorem findsg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume findsg.1: |- ( x = B -> ( ph <-> ps ) )
  assume findsg.2: |- ( x = y -> ( ph <-> ch ) )
  assume findsg.3: |- ( x = suc y -> ( ph <-> th ) )
  assume findsg.4: |- ( x = A -> ( ph <-> ta ) )
  assume findsg.5: |- ( B e. _om -> ps )
  assume findsg.6: |- ( ( ( y e. _om /\ B e. _om ) /\ B C_ y ) -> ( ch -> th ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ B C_ A ) -> ta )

  proof
    cA
    com
    wcel
    cB
    com
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
    @14
    @4
    @6
    wb
    @15
    @14
    wa
    @3
    @5
    wph
    wps
    @14
    @3
    @5
    wb
    @15
    @2
    c0
    cB
    sseq2
    #
    adantl
    @15
    @14
    wph
    wps
    wb
    #
    @15
    @14
    @2
    cB
    wceq
    #
    @17
    cB
    c0
    @2
    eqeq2
    findsg.1
    syl6bir
    imp
    imbi12d
    @14
    @4
    @5
    wph
    wi
    @15
    wn
    #
    @6
    @14
    @3
    @5
    wph
    @16
    imbi1d
    @19
    @5
    wph
    wps
    @19
    @5
    @17
    @5
    @15
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
    @20
    @3
    @8
    wph
    wch
    @2
    @7
    cB
    sseq2
    findsg.2
    imbi12d
    imbi2d
    @2
    @10
    wceq
    #
    @4
    @12
    @0
    @21
    @3
    @11
    wph
    wth
    @2
    @10
    cB
    sseq2
    findsg.3
    imbi12d
    imbi2d
    @2
    cA
    wceq
    #
    @4
    @13
    @0
    @22
    @3
    @1
    wph
    wta
    @2
    cA
    cB
    sseq2
    findsg.4
    imbi12d
    imbi2d
    @0
    wps
    @5
    findsg.5
    a1d
    @7
    com
    wcel
    #
    @0
    @9
    @12
    @23
    @0
    @9
    @12
    wi
    #
    @23
    @0
    wa
    #
    @11
    cB
    @10
    wceq
    #
    wi
    #
    @24
    @0
    @27
    @24
    wi
    @23
    @27
    @9
    @11
    @0
    wth
    @27
    @11
    @0
    wth
    wi
    #
    wi
    @9
    @26
    @28
    @11
    @28
    @10
    cB
    @10
    cB
    wceq
    @21
    @18
    wa
    #
    vx
    wex
    @28
    vx
    @10
    cB
    @7
    vy
    vex
    sucex
    eqvinc
    @29
    @28
    vx
    @18
    @0
    wph
    @21
    wth
    @0
    wph
    @18
    wps
    findsg.5
    findsg.1
    syl5ibr
    @21
    wph
    wth
    findsg.3
    biimpd
    sylan9r
    exlimiv
    sylbi
    eqcoms
    imim2i
    a1d
    com4r
    adantl
    @27
    wn
    #
    @11
    cB
    @10
    wne
    #
    wa
    #
    @25
    @24
    @32
    @11
    @26
    wn
    #
    wa
    @30
    @31
    @33
    @11
    cB
    @10
    df-ne
    anbi2i
    @11
    @26
    annim
    bitri
    @25
    @32
    @8
    @24
    @0
    cB
    con0
    wcel
    #
    @7
    con0
    wcel
    #
    @8
    @32
    wb
    @23
    cB
    nnon
    @7
    nnon
    @34
    @35
    wa
    @8
    cB
    @10
    wcel
    #
    @32
    cB
    @7
    onsssuc
    @35
    @34
    @10
    con0
    wcel
    @36
    @32
    wb
    @7
    suceloni
    cB
    @10
    onelpss
    sylan2
    bitrd
    syl2anr
    @25
    @9
    @8
    @12
    @25
    @8
    wch
    @12
    @25
    @8
    wch
    wth
    @12
    @25
    @8
    wch
    wth
    wi
    findsg.6
    ex
    wth
    @11
    ax-1
    syl8
    a2d
    com23
    sylbird
    syl5bir
    pm2.61d
    ex
    a2d
    finds
    imp31
end
