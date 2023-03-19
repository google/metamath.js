include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "ovexd.mm"
include "elexd.mm"
include "wcel.mm"
include "cvv.mm"
include "wi.mm"
include "fvexd.mm"
include "a1i.mm"
include "snex.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "mapsnd.mm"
include "abeq2d.mm"
include "anbi1d.mm"
include "wb.mm"
include "r19.41v.mm"
include "bicomi.mm"
include "df-rex.mm"
include "3bitrd.mm"
include "fveq1.mm"
include "adantl.mm"
include "vex.mm"
include "fvsng.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "equcom.mm"
include "bitrd.mm"
include "ex.mm"
include "pm5.32d.mm"
include "anbi2d.mm"
include "anass.mm"
include "ancom.mm"
include "3bitr2d.mm"
include "exbidv.mm"
include "eleq1.mm"
include "opeq2.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "en2d.mm"

theorem mapsnend
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume mapsnend.a: |- ( ph -> A e. V )
  assume mapsnend.b: |- ( ph -> B e. W )


  assert |- ( ph -> ( A ^m { B } ) ~~ A )

  proof
    wph
    vz
    vw
    cA
    cB
    csn
    #
    cmap
    co
    #
    cA
    cB
    vz
    cv
    #
    cfv
    #
    cB
    vw
    cv
    #
    cop
    #
    csn
    #
    wph
    cA
    @0
    cmap
    ovexd
    wph
    cA
    cV
    mapsnend.a
    elexd
    @2
    @1
    wcel
    #
    @3
    cvv
    wcel
    wi
    wph
    @7
    cB
    @2
    fvexd
    a1i
    @4
    cA
    wcel
    #
    @6
    cvv
    wcel
    #
    wi
    wph
    @9
    @8
    @5
    snex
    a1i
    a1i
    wph
    @7
    @4
    @3
    wceq
    #
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    @2
    cB
    @12
    cop
    #
    csn
    #
    wceq
    #
    @10
    wa
    #
    wa
    #
    vy
    wex
    #
    @12
    @4
    wceq
    #
    @13
    @16
    wa
    #
    wa
    #
    vy
    wex
    #
    @8
    @2
    @6
    wceq
    #
    wa
    #
    wph
    @11
    @16
    vy
    cA
    wrex
    #
    @10
    wa
    #
    @17
    vy
    cA
    wrex
    #
    @19
    wph
    @7
    @26
    @10
    wph
    @26
    vz
    @1
    wph
    vy
    cA
    cB
    vz
    cV
    cW
    mapsnend.a
    mapsnend.b
    mapsnd
    abeq2d
    anbi1d
    @27
    @28
    wb
    wph
    @28
    @27
    @16
    @10
    vy
    cA
    r19.41v
    bicomi
    a1i
    @28
    @19
    wb
    wph
    @17
    vy
    cA
    df-rex
    a1i
    3bitrd
    wph
    @18
    @22
    vy
    wph
    @18
    @13
    @16
    @20
    wa
    #
    wa
    #
    @21
    @20
    wa
    #
    @22
    wph
    @17
    @29
    @13
    wph
    @16
    @10
    @20
    wph
    @16
    @10
    @20
    wb
    wph
    @16
    wa
    #
    @10
    @4
    @12
    wceq
    #
    @20
    @32
    @3
    @12
    @4
    @32
    @3
    cB
    @15
    cfv
    #
    @12
    @16
    @3
    @34
    wceq
    wph
    cB
    @2
    @15
    fveq1
    adantl
    wph
    @34
    @12
    wceq
    #
    @16
    wph
    cB
    cW
    wcel
    @12
    cvv
    wcel
    #
    @35
    mapsnend.b
    @36
    wph
    vy
    vex
    a1i
    cB
    @12
    cW
    cvv
    fvsng
    syl2anc
    adantr
    eqtrd
    eqeq2d
    @33
    @20
    wb
    @32
    vw
    vy
    equcom
    a1i
    bitrd
    ex
    pm5.32d
    anbi2d
    @31
    @30
    wb
    wph
    @13
    @16
    @20
    anass
    a1i
    @31
    @22
    wb
    wph
    @21
    @20
    ancom
    a1i
    3bitr2d
    exbidv
    @23
    @25
    wb
    wph
    @21
    @25
    vy
    @4
    vw
    vex
    @20
    @13
    @8
    @16
    @24
    @12
    @4
    cA
    eleq1
    @20
    @15
    @6
    @2
    @20
    @14
    @5
    @12
    @4
    cB
    opeq2
    sneqd
    eqeq2d
    anbi12d
    ceqsexv
    a1i
    3bitrd
    en2d
end
