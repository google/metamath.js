include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "csb.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wb.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvralf.mm"
include "rabid.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"
include "bitr3i.mm"
include "rabn0.mm"
include "reusv2lem5.mm"
include "nfeq2.mm"
include "eqeq2d.mm"
include "cbvrexf.mm"
include "anbi1i.mm"
include "anass.mm"
include "rexbii2.mm"
include "reubii.mm"
include "3bitr3g.mm"
include "syl2anbr.mm"

theorem reusv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  assert |- ( ( A. y e. B ( ph -> C e. A ) /\ E. y e. B ph ) -> ( E! x e. A E. y e. B ( ph /\ x = C ) <-> E! x e. A A. y e. B ( ph -> x = C ) ) )

  proof
    wph
    cC
    cA
    wcel
    #
    wi
    #
    vy
    cB
    wral
    #
    vy
    vz
    cv
    #
    cC
    csb
    #
    cA
    wcel
    #
    vz
    wph
    vy
    cB
    crab
    #
    wral
    #
    @6
    c0
    wne
    #
    wph
    vx
    cv
    #
    cC
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    @10
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wreu
    #
    wb
    wph
    vy
    cB
    wrex
    @7
    @0
    vy
    @6
    wral
    @2
    @0
    @5
    vy
    vz
    @6
    wph
    vy
    cB
    nfrab1
    #
    vz
    @6
    nfcv
    #
    @0
    vz
    nfv
    vy
    @4
    cA
    vy
    @3
    cC
    nfcsb1v
    #
    nfel1
    vy
    cv
    #
    @3
    wceq
    #
    cC
    @4
    cA
    vy
    @3
    cC
    csbeq1a
    #
    eleq1d
    cbvralf
    @0
    @1
    vy
    @6
    cB
    @20
    @6
    wcel
    #
    @0
    wi
    @20
    cB
    wcel
    #
    wph
    wa
    #
    @0
    wi
    @24
    @1
    wi
    @23
    @25
    @0
    wph
    vy
    cB
    rabid
    #
    imbi1i
    @24
    wph
    @0
    impexp
    bitri
    ralbii2
    bitr3i
    wph
    vy
    cB
    rabn0
    @7
    @8
    wa
    @9
    @4
    wceq
    #
    vz
    @6
    wrex
    #
    vx
    cA
    wreu
    @27
    vz
    @6
    wral
    #
    vx
    cA
    wreu
    @13
    @16
    vx
    vz
    cA
    @6
    @4
    reusv2lem5
    @28
    @12
    vx
    cA
    @28
    @10
    vy
    @6
    wrex
    @12
    @10
    @27
    vy
    vz
    @6
    @17
    @18
    @10
    vz
    nfv
    #
    vy
    @9
    @4
    @19
    nfeq2
    #
    @21
    cC
    @4
    @9
    @22
    eqeq2d
    #
    cbvrexf
    @10
    @11
    vy
    @6
    cB
    @23
    @10
    wa
    @25
    @10
    wa
    @24
    @11
    wa
    @23
    @25
    @10
    @26
    anbi1i
    @24
    wph
    @10
    anass
    bitri
    rexbii2
    bitr3i
    reubii
    @29
    @15
    vx
    cA
    @29
    @10
    vy
    @6
    wral
    @15
    @10
    @27
    vy
    vz
    @6
    @17
    @18
    @30
    @31
    @32
    cbvralf
    @10
    @14
    vy
    @6
    cB
    @23
    @10
    wi
    @25
    @10
    wi
    @24
    @14
    wi
    @23
    @25
    @10
    @26
    imbi1i
    @24
    wph
    @10
    impexp
    bitri
    ralbii2
    bitr3i
    reubii
    3bitr3g
    syl2anbr
end
