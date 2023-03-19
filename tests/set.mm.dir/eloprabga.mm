include "wcel.mm"
include "cvv.mm"
include "cop.mm"
include "coprab.mm"
include "wb.mm"
include "elex.mm"
include "w3a.mm"
include "wi.mm"
include "opex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "vex.mm"
include "otth2.mm"
include "bitri.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "3exbidv.mm"
include "cab.mm"
include "df-oprab.mm"
include "eleq2i.mm"
include "abid.mm"
include "bitr2i.mm"
include "eleq1.mm"
include "syl5bb.mm"
include "adantl.mm"
include "elisset.mm"
include "3anim123i.mm"
include "eeeanv.mm"
include "sylibr.mm"
include "biantrurd.mm"
include "19.41vvv.mm"
include "syl6rbbr.mm"
include "adantr.mm"
include "3bitr3d.mm"
include "expcom.mm"
include "vtocle.mm"
include "syl3an.mm"

theorem eloprabga
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  assume eloprabga.1: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint ph w
  disjoint ps w
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> ps ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cB
    cW
    wcel
    cB
    cvv
    wcel
    #
    cC
    cX
    wcel
    cC
    cvv
    wcel
    #
    cA
    cB
    cop
    #
    cC
    cop
    #
    wph
    vx
    vy
    vz
    coprab
    #
    wcel
    #
    wps
    wb
    #
    cA
    cV
    elex
    cB
    cW
    elex
    cC
    cX
    elex
    @0
    @1
    @2
    w3a
    #
    @7
    wi
    vw
    @4
    @3
    cC
    opex
    @8
    vw
    cv
    #
    @4
    wceq
    #
    @7
    @8
    @10
    wa
    #
    @9
    vx
    cv
    #
    vy
    cv
    #
    cop
    vz
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    @12
    cA
    wceq
    #
    @13
    cB
    wceq
    #
    @14
    cC
    wceq
    #
    w3a
    #
    wps
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    @6
    wps
    @11
    @17
    @23
    vx
    vy
    vz
    @11
    @17
    @22
    wph
    wa
    @23
    @11
    @16
    @22
    wph
    @11
    @16
    @4
    @15
    wceq
    #
    @22
    @11
    @9
    @4
    @15
    @8
    @10
    simpr
    eqeq1d
    @25
    @15
    @4
    wceq
    @22
    @4
    @15
    eqcom
    @12
    @13
    cA
    cB
    @14
    cC
    vx
    vex
    vy
    vex
    vz
    vex
    otth2
    bitri
    syl6bb
    anbi1d
    @22
    wph
    wps
    eloprabga.1
    pm5.32i
    syl6bb
    3exbidv
    @10
    @18
    @6
    wb
    @8
    @18
    @9
    @5
    wcel
    #
    @10
    @6
    @26
    @9
    @18
    vw
    cab
    #
    wcel
    @18
    @5
    @27
    @9
    wph
    vx
    vy
    vz
    vw
    df-oprab
    eleq2i
    @18
    vw
    abid
    bitr2i
    @9
    @4
    @5
    eleq1
    syl5bb
    adantl
    @8
    @24
    wps
    wb
    @10
    @8
    wps
    @22
    vz
    wex
    vy
    wex
    vx
    wex
    #
    wps
    wa
    @24
    @8
    @28
    wps
    @8
    @19
    vx
    wex
    #
    @20
    vy
    wex
    #
    @21
    vz
    wex
    #
    w3a
    @28
    @0
    @29
    @1
    @30
    @2
    @31
    vx
    cA
    cvv
    elisset
    vy
    cB
    cvv
    elisset
    vz
    cC
    cvv
    elisset
    3anim123i
    @19
    @20
    @21
    vx
    vy
    vz
    eeeanv
    sylibr
    biantrurd
    @22
    wps
    vx
    vy
    vz
    19.41vvv
    syl6rbbr
    adantr
    3bitr3d
    expcom
    vtocle
    syl3an
end
