include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "wral.mm"
include "wreu.mm"
include "wi.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "clt.mm"
include "cn.mm"
include "wss.mm"
include "nnssz.mm"
include "arch.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "zre.mm"
include "ltle.mm"
include "sylan2.mm"
include "reximdva.mm"
include "mpd.mm"
include "rabn0.mm"
include "sylibr.mm"
include "breq2.mm"
include "cbvrabv.mm"
include "eqimssi.mm"
include "uzwo3.mm"
include "mpanr1.mm"
include "mpdan.mm"
include "weu.mm"
include "elrab.mm"
include "ralrab.mm"
include "anbi12i.mm"
include "anass.mm"
include "bitri.mm"
include "eubii.mm"
include "df-reu.mm"
include "3bitr4i.mm"
include "sylib.mm"

theorem zmin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A e. RR -> E! x e. ZZ ( A <_ x /\ A. y e. ZZ ( A <_ y -> x <_ y ) ) )

  proof
    cA
    cr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cz
    crab
    #
    wral
    #
    vx
    @6
    wreu
    #
    cA
    @1
    cle
    wbr
    #
    cA
    @2
    cle
    wbr
    #
    @3
    wi
    vy
    cz
    wral
    #
    wa
    #
    vx
    cz
    wreu
    #
    @0
    @6
    c0
    wne
    #
    @8
    @0
    @5
    vz
    cz
    wrex
    #
    @14
    @0
    cA
    @4
    clt
    wbr
    #
    vz
    cz
    wrex
    #
    @15
    cn
    cz
    wss
    @0
    @16
    vz
    cn
    wrex
    @17
    nnssz
    cA
    vz
    arch
    @16
    vz
    cn
    cz
    ssrexv
    mpsyl
    @0
    @16
    @5
    vz
    cz
    @4
    cz
    wcel
    @0
    @4
    cr
    wcel
    @16
    @5
    wi
    @4
    zre
    cA
    @4
    ltle
    sylan2
    reximdva
    mpd
    @5
    vz
    cz
    rabn0
    sylibr
    @0
    @6
    cA
    vn
    cv
    #
    cle
    wbr
    #
    vn
    cz
    crab
    #
    wss
    @14
    @8
    @6
    @20
    @5
    @19
    vz
    vn
    cz
    @4
    @18
    cA
    cle
    breq2
    cbvrabv
    eqimssi
    vx
    vy
    vn
    @6
    cA
    uzwo3
    mpanr1
    mpdan
    @1
    @6
    wcel
    #
    @7
    wa
    #
    vx
    weu
    @1
    cz
    wcel
    #
    @12
    wa
    #
    vx
    weu
    @8
    @13
    @22
    @24
    vx
    @22
    @23
    @9
    wa
    #
    @11
    wa
    @24
    @21
    @25
    @7
    @11
    @5
    @9
    vz
    @1
    cz
    @4
    @1
    cA
    cle
    breq2
    elrab
    @5
    @10
    @3
    vy
    vz
    cz
    @4
    @2
    cA
    cle
    breq2
    ralrab
    anbi12i
    @23
    @9
    @11
    anass
    bitri
    eubii
    @7
    vx
    @6
    df-reu
    @12
    vx
    cz
    df-reu
    3bitr4i
    sylib
end
