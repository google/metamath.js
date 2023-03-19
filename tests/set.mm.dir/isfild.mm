include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cfil.mm"
include "cfv.mm"
include "wa.mm"
include "selpw.mm"
include "biimpri.mm"
include "adantr.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "wsbc.mm"
include "isfildlem.mm"
include "simpr.mm"
include "mtod.mm"
include "ssid.mm"
include "jctil.mm"
include "mpbird.mm"
include "3jca.mm"
include "elpwi.mm"
include "simp2.mm"
include "jctild.mm"
include "adantld.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "3imtr4d.mm"
include "3expa.mm"
include "impancom.mm"
include "rexlimdva.mm"
include "ex.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "ssinss1.mm"
include "ad2antrr.mm"
include "a1i.mm"
include "an4.mm"
include "3expb.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "jcad.mm"
include "anbi12d.mm"
include "ralrimivv.mm"
include "isfil2.mm"
include "syl3anbrc.mm"

theorem isfild
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cB: class B
  assume isfild.1: |- ( ph -> ( x e. F <-> ( x C_ A /\ ps ) ) )
  assume isfild.2: |- ( ph -> A e. _V )
  assume isfild.3: |- ( ph -> [. A / x ]. ps )
  assume isfild.4: |- ( ph -> -. [. (/) / x ]. ps )
  assume isfild.5: |- ( ( ph /\ y C_ A /\ z C_ y ) -> ( [. z / x ]. ps -> [. y / x ]. ps ) )
  assume isfild.6: |- ( ( ph /\ y C_ A /\ z C_ A ) -> ( ( [. y / x ]. ps /\ [. z / x ]. ps ) -> [. ( y i^i z ) / x ]. ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint y z
  disjoint F z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint B y
  assert |- ( ph -> F e. ( Fil ` A ) )

  proof
    wph
    cF
    cA
    cpw
    #
    wss
    #
    c0
    cF
    wcel
    #
    wn
    #
    cA
    cF
    wcel
    #
    w3a
    vz
    cv
    #
    vy
    cv
    #
    wss
    #
    vz
    cF
    wrex
    @6
    cF
    wcel
    #
    wi
    #
    vy
    @0
    wral
    @6
    @5
    cin
    #
    cF
    wcel
    #
    vz
    cF
    wral
    vy
    cF
    wral
    cF
    cA
    cfil
    cfv
    wcel
    wph
    @1
    @3
    @4
    wph
    vx
    cF
    @0
    wph
    vx
    cv
    #
    cF
    wcel
    @12
    cA
    wss
    #
    wps
    wa
    @12
    @0
    wcel
    #
    isfild.1
    @13
    @14
    wps
    @14
    @13
    vx
    cA
    selpw
    biimpri
    adantr
    syl6bi
    ssrdv
    wph
    @2
    wps
    vx
    c0
    wsbc
    #
    isfild.4
    wph
    @2
    c0
    cA
    wss
    #
    @15
    wa
    @15
    wph
    wps
    vx
    cA
    c0
    cF
    isfild.1
    isfild.2
    isfildlem
    @16
    @15
    simpr
    syl6bi
    mtod
    wph
    @4
    cA
    cA
    wss
    #
    wps
    vx
    cA
    wsbc
    #
    wa
    wph
    @18
    @17
    isfild.3
    cA
    ssid
    jctil
    wph
    wps
    vx
    cA
    cA
    cF
    isfild.1
    isfild.2
    isfildlem
    mpbird
    3jca
    wph
    @9
    vy
    @0
    @6
    @0
    wcel
    @6
    cA
    wss
    #
    wph
    @9
    @6
    cA
    elpwi
    wph
    @19
    @9
    wph
    @19
    wa
    #
    @7
    @8
    vz
    cF
    @20
    @7
    @5
    cF
    wcel
    #
    @8
    wph
    @19
    @7
    @21
    @8
    wi
    wph
    @19
    @7
    w3a
    #
    @5
    cA
    wss
    #
    wps
    vx
    @5
    wsbc
    #
    wa
    #
    @19
    wps
    vx
    @6
    wsbc
    #
    wa
    #
    @21
    @8
    @22
    @24
    @27
    @23
    @22
    @24
    @26
    @19
    isfild.5
    wph
    @19
    @7
    simp2
    jctild
    adantld
    wph
    @19
    @21
    @25
    wb
    @7
    wph
    wps
    vx
    cA
    @5
    cF
    isfild.1
    isfild.2
    isfildlem
    #
    3ad2ant1
    wph
    @19
    @8
    @27
    wb
    @7
    wph
    wps
    vx
    cA
    @6
    cF
    isfild.1
    isfild.2
    isfildlem
    #
    3ad2ant1
    3imtr4d
    3expa
    impancom
    rexlimdva
    ex
    syl5
    ralrimiv
    wph
    @11
    vy
    vz
    cF
    cF
    wph
    @27
    @25
    wa
    #
    @10
    cA
    wss
    #
    wps
    vx
    @10
    wsbc
    #
    wa
    @8
    @21
    wa
    @11
    wph
    @30
    @31
    @32
    @30
    @31
    wi
    wph
    @19
    @31
    @26
    @25
    @6
    @5
    cA
    ssinss1
    ad2antrr
    a1i
    @30
    @19
    @23
    wa
    #
    @26
    @24
    wa
    #
    wa
    wph
    @32
    @19
    @26
    @23
    @24
    an4
    wph
    @33
    @34
    @32
    wph
    @19
    @23
    @34
    @32
    wi
    isfild.6
    3expb
    expimpd
    syl5bi
    jcad
    wph
    @8
    @27
    @21
    @25
    @29
    @28
    anbi12d
    wph
    wps
    vx
    cA
    @10
    cF
    isfild.1
    isfild.2
    isfildlem
    3imtr4d
    ralrimivv
    vy
    vz
    cF
    cA
    isfil2
    syl3anbrc
end
