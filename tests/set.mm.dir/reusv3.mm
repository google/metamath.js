include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "nfra2.mm"
include "nfv.mm"
include "nfim.mm"
include "risset.mm"
include "ralcom.mm"
include "impexp.mm"
include "bi2.04.mm"
include "bitri.mm"
include "ralbii.mm"
include "r19.21v.mm"
include "rsp.mm"
include "sylbi.mm"
include "com3l.mm"
include "imp31.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "reximdv.mm"
include "ex.mm"
include "com23.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimi.mm"
include "reusv3i.mm"
include "impbid1.mm"

theorem reusv3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume reusv3.1: |- ( y = z -> ( ph <-> ps ) )
  assume reusv3.2: |- ( y = z -> C = D )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph z
  disjoint ps x
  disjoint ps y
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( E. y e. B ( ph /\ C e. A ) -> ( A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D ) <-> E. x e. A A. y e. B ( ph -> x = C ) ) )

  proof
    wph
    cC
    cA
    wcel
    #
    wa
    #
    vy
    cB
    wrex
    #
    wph
    wps
    wa
    cC
    cD
    wceq
    #
    wi
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wph
    vx
    cv
    #
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wrex
    #
    @2
    wps
    cD
    cA
    wcel
    #
    wa
    #
    vz
    cB
    wrex
    @5
    @10
    wi
    #
    @1
    @12
    vy
    vz
    cB
    vy
    cv
    vz
    cv
    #
    wceq
    #
    wph
    wps
    @0
    @11
    reusv3.1
    @15
    cC
    cD
    cA
    reusv3.2
    eleq1d
    anbi12d
    cbvrexv
    @12
    @13
    vz
    cB
    @5
    @10
    vz
    @4
    vy
    vz
    cB
    cB
    nfra2
    @10
    vz
    nfv
    nfim
    @14
    cB
    wcel
    #
    wps
    @11
    @13
    @11
    @6
    cD
    wceq
    #
    vx
    cA
    wrex
    #
    @16
    wps
    wa
    #
    @13
    vx
    cD
    cA
    risset
    @19
    @5
    @18
    @10
    @19
    @5
    @18
    @10
    wi
    @19
    @5
    wa
    #
    @17
    @9
    vx
    cA
    @20
    @9
    @17
    wph
    @3
    wi
    #
    vy
    cB
    wral
    #
    @16
    wps
    @5
    @22
    @5
    @16
    wps
    @22
    @5
    wps
    @22
    wi
    #
    vz
    cB
    wral
    #
    @16
    @23
    wi
    @5
    @4
    vy
    cB
    wral
    #
    vz
    cB
    wral
    @24
    @4
    vy
    vz
    cB
    cB
    ralcom
    @25
    @23
    vz
    cB
    @25
    wps
    @21
    wi
    #
    vy
    cB
    wral
    @23
    @4
    @26
    vy
    cB
    @4
    wph
    wps
    @3
    wi
    wi
    @26
    wph
    wps
    @3
    impexp
    wph
    wps
    @3
    bi2.04
    bitri
    ralbii
    wps
    @21
    vy
    cB
    r19.21v
    bitri
    ralbii
    bitri
    @23
    vz
    cB
    rsp
    sylbi
    com3l
    imp31
    @17
    @8
    @21
    vy
    cB
    @17
    @7
    @3
    wph
    @17
    @7
    cD
    cC
    wceq
    @3
    @6
    cD
    cC
    eqeq1
    cD
    cC
    eqcom
    syl6bb
    imbi2d
    ralbidv
    syl5ibrcom
    reximdv
    ex
    com23
    syl5bi
    expimpd
    rexlimi
    sylbi
    wph
    wps
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    reusv3.1
    reusv3.2
    reusv3i
    impbid1
end
