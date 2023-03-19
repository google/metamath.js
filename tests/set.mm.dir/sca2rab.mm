include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wceq.mm"
include "adantr.mm"
include "eleq2d.mm"
include "wb.mm"
include "crp.mm"
include "rprecred.mm"
include "remulcl.mm"
include "sylancom.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "simpr.mm"
include "recnd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrec2d.mm"
include "oveq2d.mm"
include "divcan2d.mm"
include "eqtr3d.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem sca2rab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cR: class R
  let vm: setvar m
  let cS: class S
  assume ovolsca.1: |- ( ph -> A C_ RR )
  assume ovolsca.2: |- ( ph -> C e. RR+ )
  assume ovolsca.3: |- ( ph -> B = { x e. RR | ( C x. x ) e. A } )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph y
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint B f
  disjoint B n
  disjoint F n
  disjoint F x
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint f m
  disjoint C f
  disjoint k m
  disjoint C k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint C n
  disjoint f ph
  disjoint k ph
  disjoint n ph
  disjoint S k
  disjoint S x
  assert |- ( ph -> A = { y e. RR | ( ( 1 / C ) x. y ) e. B } )

  proof
    wph
    cA
    vy
    cv
    #
    cr
    wcel
    #
    c1
    cC
    cdiv
    co
    #
    @0
    cmul
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    cab
    @4
    vy
    cr
    crab
    wph
    @5
    vy
    cA
    wph
    @0
    cA
    wcel
    #
    @1
    @6
    wa
    @5
    wph
    @6
    @1
    wph
    cA
    cr
    @0
    ovolsca.1
    sseld
    pm4.71rd
    wph
    @1
    @4
    @6
    wph
    @1
    wa
    #
    @4
    @3
    cC
    vx
    cv
    #
    cmul
    co
    #
    cA
    wcel
    #
    vx
    cr
    crab
    #
    wcel
    #
    cC
    @3
    cmul
    co
    #
    cA
    wcel
    #
    @6
    @7
    cB
    @11
    @3
    wph
    cB
    @11
    wceq
    @1
    ovolsca.3
    adantr
    eleq2d
    @7
    @3
    cr
    wcel
    #
    @12
    @14
    wb
    wph
    @1
    @2
    cr
    wcel
    @15
    @7
    cC
    wph
    cC
    crp
    wcel
    @1
    ovolsca.2
    adantr
    #
    rprecred
    @2
    @0
    remulcl
    sylancom
    @10
    @14
    vx
    @3
    cr
    @8
    @3
    wceq
    @9
    @13
    cA
    @8
    @3
    cC
    cmul
    oveq2
    eleq1d
    elrab3
    syl
    @7
    @13
    @0
    cA
    @7
    cC
    @0
    cC
    cdiv
    co
    #
    cmul
    co
    @13
    @0
    @7
    @17
    @3
    cC
    cmul
    @7
    @0
    cC
    @7
    @0
    wph
    @1
    simpr
    recnd
    #
    @7
    cC
    @16
    rpcnd
    #
    @7
    cC
    @16
    rpne0d
    #
    divrec2d
    oveq2d
    @7
    @0
    cC
    @18
    @19
    @20
    divcan2d
    eqtr3d
    eleq1d
    3bitrd
    pm5.32da
    bitr4d
    abbi2dv
    @4
    vy
    cr
    df-rab
    syl6eqr
end
