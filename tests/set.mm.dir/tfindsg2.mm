include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "wss.mm"
include "onelon.mm"
include "sucelon.mm"
include "sylib.mm"
include "word.mm"
include "wi.mm"
include "eloni.mm"
include "ordsucss.mm"
include "syl.mm"
include "imp.mm"
include "sylbir.mm"
include "cv.mm"
include "wb.mm"
include "ordelsuc.mm"
include "sylan2.mm"
include "ancoms.mm"
include "ex.mm"
include "adantr.mm"
include "sylbird.mm"
include "sylan2br.mm"
include "wlim.mm"
include "wral.mm"
include "cvv.mm"
include "vex.mm"
include "limelon.mm"
include "mpan.mm"
include "anassrs.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "imbi12d.mm"
include "mpbid.mm"
include "tfindsg.mm"
include "expl.mm"
include "mp2and.mm"

theorem tfindsg2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume tfindsg2.1: |- ( x = suc B -> ( ph <-> ps ) )
  assume tfindsg2.2: |- ( x = y -> ( ph <-> ch ) )
  assume tfindsg2.3: |- ( x = suc y -> ( ph <-> th ) )
  assume tfindsg2.4: |- ( x = A -> ( ph <-> ta ) )
  assume tfindsg2.5: |- ( B e. On -> ps )
  assume tfindsg2.6: |- ( ( y e. On /\ B e. y ) -> ( ch -> th ) )
  assume tfindsg2.7: |- ( ( Lim x /\ B e. x ) -> ( A. y e. x ( B e. y -> ch ) -> ph ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( ( A e. On /\ B e. A ) -> ta )

  proof
    cA
    con0
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    csuc
    #
    con0
    wcel
    #
    @3
    cA
    wss
    #
    wta
    @2
    cB
    con0
    wcel
    #
    @4
    cA
    cB
    onelon
    cB
    sucelon
    #
    sylib
    @0
    @1
    @5
    @0
    cA
    word
    @1
    @5
    wi
    cA
    eloni
    cB
    cA
    ordsucss
    syl
    imp
    @0
    @4
    @5
    wa
    wta
    wi
    @1
    @0
    @4
    @5
    wta
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cA
    @3
    tfindsg2.1
    tfindsg2.2
    tfindsg2.3
    tfindsg2.4
    @4
    @6
    wps
    @7
    tfindsg2.5
    sylbir
    vy
    cv
    #
    con0
    wcel
    #
    @4
    wa
    @3
    @8
    wss
    #
    wch
    wth
    wi
    #
    @4
    @9
    @6
    @10
    @11
    wi
    @7
    @9
    @6
    wa
    @10
    cB
    @8
    wcel
    #
    @11
    @6
    @9
    @12
    @10
    wb
    #
    @9
    @6
    @8
    word
    #
    @13
    @8
    eloni
    #
    cB
    @8
    con0
    ordelsuc
    #
    sylan2
    ancoms
    @9
    @12
    @11
    wi
    @6
    @9
    @12
    @11
    tfindsg2.6
    ex
    adantr
    sylbird
    sylan2br
    imp
    vx
    cv
    #
    wlim
    #
    @4
    wa
    @3
    @17
    wss
    #
    @10
    wch
    wi
    #
    vy
    @17
    wral
    #
    wph
    wi
    #
    @4
    @18
    @6
    @19
    @22
    wi
    #
    @7
    @18
    @6
    wa
    cB
    @17
    wcel
    #
    @12
    wch
    wi
    #
    vy
    @17
    wral
    #
    wph
    wi
    #
    wi
    #
    @23
    @18
    @28
    @6
    @18
    @24
    @27
    tfindsg2.7
    ex
    adantr
    @6
    @18
    @28
    @23
    wb
    #
    @18
    @6
    @17
    con0
    wcel
    #
    @29
    @17
    cvv
    wcel
    @18
    @30
    vx
    vex
    @17
    cvv
    limelon
    mpan
    @6
    @30
    wa
    #
    @24
    @19
    @27
    @22
    @30
    @6
    @17
    word
    @24
    @19
    wb
    @17
    eloni
    cB
    @17
    con0
    ordelsuc
    sylan2
    @31
    @26
    @21
    wph
    @31
    @25
    @20
    vy
    @17
    @31
    @8
    @17
    wcel
    #
    wa
    @12
    @10
    wch
    @6
    @30
    @32
    @13
    @30
    @32
    wa
    #
    @6
    @14
    @13
    @33
    @9
    @14
    @17
    @8
    onelon
    @15
    syl
    @16
    sylan2
    anassrs
    imbi1d
    ralbidva
    imbi1d
    imbi12d
    sylan2
    ancoms
    mpbid
    sylan2br
    imp
    tfindsg
    expl
    adantr
    mp2and
end
