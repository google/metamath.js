include "cxp.mm"
include "cin.mm"
include "wrel.mm"
include "wss.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "simpr.mm"
include "brinxp2.mm"
include "sylib.mm"
include "simp2d.mm"
include "simp1d.mm"
include "wer.mm"
include "adantr.mm"
include "simp3d.mm"
include "ersym.mm"
include "syl3anbrc.mm"
include "adantrr.mm"
include "simprr.mm"
include "ertrd.mm"
include "sselda.mm"
include "erref.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "brin.mm"
include "brxp.mm"
include "anidm.mm"
include "bitri.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "iserd.mm"

theorem erinxp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume erinxp.r: |- ( ph -> R Er A )
  assume erinxp.a: |- ( ph -> B C_ A )


  assert |- ( ph -> ( R i^i ( B X. B ) ) Er B )

  proof
    wph
    vx
    vy
    vz
    cB
    cR
    cB
    cB
    cxp
    #
    cin
    #
    @1
    wrel
    #
    wph
    @1
    @0
    wss
    @0
    wrel
    @2
    cR
    @0
    inss2
    cB
    cB
    relxp
    @1
    @0
    relss
    mp2
    a1i
    wph
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    #
    wa
    #
    @4
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    @4
    @3
    cR
    wbr
    @4
    @3
    @1
    wbr
    @6
    @8
    @7
    @3
    @4
    cR
    wbr
    #
    @6
    @5
    @8
    @7
    @9
    w3a
    wph
    @5
    simpr
    @3
    @4
    cB
    cB
    cR
    brinxp2
    sylib
    #
    simp2d
    @6
    @8
    @7
    @9
    @10
    simp1d
    #
    @6
    @3
    @4
    cR
    cA
    wph
    cA
    cR
    wer
    #
    @5
    erinxp.r
    adantr
    @6
    @8
    @7
    @9
    @10
    simp3d
    #
    ersym
    @4
    @3
    cB
    cB
    cR
    brinxp2
    syl3anbrc
    wph
    @5
    @4
    vz
    cv
    #
    @1
    wbr
    #
    wa
    #
    wa
    #
    @8
    @14
    cB
    wcel
    #
    @3
    @14
    cR
    wbr
    @3
    @14
    @1
    wbr
    wph
    @5
    @8
    @15
    @11
    adantrr
    @17
    @7
    @18
    @4
    @14
    cR
    wbr
    #
    @17
    @15
    @7
    @18
    @19
    w3a
    wph
    @5
    @15
    simprr
    @4
    @14
    cB
    cB
    cR
    brinxp2
    sylib
    #
    simp2d
    @17
    @3
    @4
    @14
    cR
    cA
    wph
    @12
    @16
    erinxp.r
    adantr
    wph
    @5
    @9
    @15
    @13
    adantrr
    @17
    @7
    @18
    @19
    @20
    simp3d
    ertrd
    @3
    @14
    cB
    cB
    cR
    brinxp2
    syl3anbrc
    wph
    @8
    @3
    @3
    cR
    wbr
    #
    @8
    wa
    #
    @3
    @3
    @1
    wbr
    #
    wph
    @8
    @21
    wph
    @8
    @21
    wph
    @8
    wa
    @3
    cR
    cA
    wph
    @12
    @8
    erinxp.r
    adantr
    wph
    cB
    cA
    @3
    erinxp.a
    sselda
    erref
    ex
    pm4.71rd
    @23
    @21
    @3
    @3
    @0
    wbr
    #
    wa
    @22
    @3
    @3
    cR
    @0
    brin
    @24
    @8
    @21
    @24
    @8
    @8
    wa
    @8
    @3
    @3
    cB
    cB
    brxp
    @8
    anidm
    bitri
    anbi2i
    bitri
    syl6bbr
    iserd
end
