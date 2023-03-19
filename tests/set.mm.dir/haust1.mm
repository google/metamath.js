include "cha.mm"
include "wcel.mm"
include "ct1.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "cuni.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "cin.mm"
include "c0.mm"
include "eqid.mm"
include "hausnei.mm"
include "simprr1.mm"
include "noel.mm"
include "simprr3.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "simprr2.mm"
include "elin.mm"
include "simplbi2com.mm"
include "syl.mm"
include "mtod.mm"
include "jca.mm"
include "rexlimdvaa.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexanali.mm"
include "sylib.mm"
include "3exp2.mm"
include "imp32.mm"
include "necon4ad.mm"
include "ralrimivva.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "ctop.mm"
include "haustop.mm"
include "toptopon.mm"
include "ist1-2.mm"
include "mpbird.mm"

theorem haust1
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( J e. Haus -> J e. Fre )

  proof
    cJ
    cha
    wcel
    #
    cJ
    ct1
    wcel
    #
    vx
    vz
    wel
    #
    vy
    vz
    wel
    #
    wi
    vz
    cJ
    wral
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    wi
    #
    vy
    cJ
    cuni
    #
    wral
    vx
    @8
    wral
    #
    @0
    @7
    vx
    vy
    @8
    @8
    @0
    @5
    @8
    wcel
    #
    @6
    @8
    wcel
    #
    wa
    wa
    @4
    @5
    @6
    @0
    @10
    @11
    @5
    @6
    wne
    #
    @4
    wn
    #
    wi
    @0
    @10
    @11
    @12
    @13
    @0
    @10
    @11
    @12
    w3a
    wa
    #
    @2
    @3
    wn
    #
    wa
    #
    vz
    cJ
    wrex
    #
    @13
    @14
    @2
    vy
    vw
    wel
    #
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vw
    cJ
    wrex
    #
    vz
    cJ
    wrex
    @17
    @5
    @6
    vw
    vz
    cJ
    @8
    @8
    eqid
    #
    hausnei
    @14
    @24
    @16
    vz
    cJ
    @14
    @19
    cJ
    wcel
    wa
    #
    @23
    @16
    vw
    cJ
    @26
    @20
    cJ
    wcel
    #
    @23
    wa
    wa
    #
    @2
    @15
    @2
    @18
    @22
    @27
    @26
    simprr1
    @28
    @3
    @6
    @21
    wcel
    #
    @28
    @29
    @6
    c0
    wcel
    @6
    noel
    @28
    @21
    c0
    @6
    @2
    @18
    @22
    @27
    @26
    simprr3
    eleq2d
    mtbiri
    @28
    @18
    @3
    @29
    wi
    @2
    @18
    @22
    @27
    @26
    simprr2
    @29
    @3
    @18
    @6
    @19
    @20
    elin
    simplbi2com
    syl
    mtod
    jca
    rexlimdvaa
    reximdva
    mpd
    @2
    @3
    vz
    cJ
    rexanali
    sylib
    3exp2
    imp32
    necon4ad
    ralrimivva
    @0
    cJ
    @8
    ctopon
    cfv
    wcel
    #
    @1
    @9
    wb
    @0
    cJ
    ctop
    wcel
    @30
    cJ
    haustop
    cJ
    @8
    @25
    toptopon
    sylib
    vx
    vy
    vz
    cJ
    @8
    ist1-2
    syl
    mpbird
end
