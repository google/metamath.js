include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wss.mm"
include "adantr.mm"
include "simprr.mm"
include "sseldd.mm"
include "simprl.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "vex.mm"
include "weq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "anbi2d.mm"
include "wb.mm"
include "breq12.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "ancom.mm"
include "syl5bb.mm"
include "equcom.mm"
include "syl2anb.mm"
include "bicomd.mm"
include "w3a.mm"
include "df-3an.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "vtocl2.mm"
include "lecasei.mm"

theorem wloglei
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  assume wlogle.1: |- ( ( z = x /\ w = y ) -> ( ps <-> ch ) )
  assume wlogle.2: |- ( ( z = y /\ w = x ) -> ( ps <-> th ) )
  assume wlogle.3: |- ( ph -> S C_ RR )
  assume wloglei.4: |- ( ( ph /\ ( x e. S /\ y e. S /\ x <_ y ) ) -> th )
  assume wloglei.5: |- ( ( ph /\ ( x e. S /\ y e. S /\ x <_ y ) ) -> ch )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ps x
  disjoint ps y
  disjoint ch w
  disjoint ch z
  assert |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ch )

  proof
    wph
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    #
    wa
    #
    wch
    @2
    @0
    @5
    cS
    cr
    @2
    wph
    cS
    cr
    wss
    @4
    wlogle.3
    adantr
    #
    wph
    @1
    @3
    simprr
    sseldd
    @5
    cS
    cr
    @0
    @6
    wph
    @1
    @3
    simprl
    sseldd
    wph
    vz
    cv
    #
    cS
    wcel
    #
    vw
    cv
    #
    cS
    wcel
    #
    wa
    #
    wa
    #
    @9
    @7
    cle
    wbr
    #
    wa
    #
    wps
    wi
    #
    @5
    @2
    @0
    cle
    wbr
    #
    wa
    #
    wch
    wi
    vz
    vw
    @0
    @2
    vx
    vex
    vy
    vex
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    @14
    @17
    wps
    wch
    @20
    @12
    @5
    @13
    @16
    @20
    @11
    @4
    wph
    @18
    @8
    @1
    @19
    @10
    @3
    @7
    @0
    cS
    eleq1
    @9
    @2
    cS
    eleq1
    bi2anan9
    anbi2d
    @19
    @18
    @13
    @16
    wb
    @9
    @2
    @7
    @0
    cle
    breq12
    ancoms
    anbi12d
    wlogle.1
    imbi12d
    @5
    @0
    @2
    cle
    wbr
    #
    wa
    #
    wth
    wi
    @15
    vy
    vx
    @7
    @9
    vz
    vex
    vw
    vex
    vy
    vz
    weq
    #
    vx
    vw
    weq
    #
    wa
    #
    @22
    @14
    wth
    wps
    @25
    @5
    @12
    @21
    @13
    @25
    @4
    @11
    wph
    @4
    @3
    @1
    wa
    @25
    @11
    @1
    @3
    ancom
    @23
    @3
    @8
    @24
    @1
    @10
    @2
    @7
    cS
    eleq1
    @0
    @9
    cS
    eleq1
    bi2anan9
    syl5bb
    anbi2d
    @24
    @23
    @21
    @13
    wb
    @0
    @9
    @2
    @7
    cle
    breq12
    ancoms
    anbi12d
    @25
    wps
    wth
    @23
    vz
    vy
    weq
    vw
    vx
    weq
    wps
    wth
    wb
    @24
    vy
    vz
    equcom
    vx
    vw
    equcom
    wlogle.2
    syl2anb
    bicomd
    imbi12d
    wph
    @4
    @21
    wth
    @4
    @21
    wa
    #
    wph
    @1
    @3
    @21
    w3a
    #
    wth
    @1
    @3
    @21
    df-3an
    #
    wloglei.4
    sylan2br
    anassrs
    vtocl2
    vtocl2
    wph
    @4
    @21
    wch
    @26
    wph
    @27
    wch
    @28
    wloglei.5
    sylan2br
    anassrs
    lecasei
end
