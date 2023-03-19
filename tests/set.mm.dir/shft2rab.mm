include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "recnd.mm"
include "subneg.mm"
include "syl2anr.mm"
include "adantr.mm"
include "eleq12d.mm"
include "wb.mm"
include "id.mm"
include "readdcl.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "pncan.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem shft2rab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cM: class M
  assume ovolshft.1: |- ( ph -> A C_ RR )
  assume ovolshft.2: |- ( ph -> C e. RR )
  assume ovolshft.3: |- ( ph -> B = { x e. RR | ( x - C ) e. A } )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint B y
  disjoint ph y
  disjoint f g
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f m
  disjoint C f
  disjoint g m
  disjoint C g
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint C n
  disjoint C w
  disjoint C z
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G n
  disjoint G y
  disjoint B f
  disjoint B g
  disjoint B n
  disjoint B w
  disjoint B z
  disjoint M g
  disjoint M z
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> A = { y e. RR | ( y - -u C ) e. B } )

  proof
    wph
    cA
    vy
    cv
    #
    cr
    wcel
    #
    @0
    cC
    cneg
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    cab
    @3
    vy
    cr
    crab
    wph
    @4
    vy
    cA
    wph
    @0
    cA
    wcel
    #
    @1
    @5
    wa
    @4
    wph
    @5
    @1
    wph
    cA
    cr
    @0
    ovolshft.1
    sseld
    pm4.71rd
    wph
    @1
    @3
    @5
    wph
    @1
    wa
    #
    @3
    @0
    cC
    caddc
    co
    #
    vx
    cv
    #
    cC
    cmin
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
    @7
    cC
    cmin
    co
    #
    cA
    wcel
    #
    @5
    @6
    @2
    @7
    cB
    @11
    @1
    @0
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @2
    @7
    wceq
    wph
    @0
    recn
    #
    wph
    cC
    ovolshft.2
    recnd
    #
    @0
    cC
    subneg
    syl2anr
    wph
    cB
    @11
    wceq
    @1
    ovolshft.3
    adantr
    eleq12d
    @6
    @7
    cr
    wcel
    #
    @12
    @14
    wb
    @1
    @1
    cC
    cr
    wcel
    @19
    wph
    @1
    id
    ovolshft.2
    @0
    cC
    readdcl
    syl2anr
    @10
    @14
    vx
    @7
    cr
    @8
    @7
    wceq
    @9
    @13
    cA
    @8
    @7
    cC
    cmin
    oveq1
    eleq1d
    elrab3
    syl
    @6
    @13
    @0
    cA
    @1
    @15
    @16
    @13
    @0
    wceq
    wph
    @17
    @18
    @0
    cC
    pncan
    syl2anr
    eleq1d
    3bitrd
    pm5.32da
    bitr4d
    abbi2dv
    @3
    vy
    cr
    df-rab
    syl6eqr
end
