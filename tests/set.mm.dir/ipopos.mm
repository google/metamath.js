include "cvv.mm"
include "wcel.mm"
include "cpo.mm"
include "cple.mm"
include "cfv.mm"
include "cipo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ipobas.mm"
include "eqidd.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wss.mm"
include "ssid.mm"
include "wb.mm"
include "eqid.mm"
include "ipole.mm"
include "3anidm23.mm"
include "mpbiri.mm"
include "w3a.mm"
include "weq.mm"
include "3com23.mm"
include "anbi12d.mm"
include "simpl.mm"
include "simpr.mm"
include "eqssd.mm"
include "syl6bi.mm"
include "wi.mm"
include "sstr.mm"
include "3adant3r3.mm"
include "3adant3r1.mm"
include "3adant3r2.mm"
include "3imtr4d.mm"
include "isposd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "0pos.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem ipopos
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume ipopos.i: |- I = ( toInc ` F )


  assert |- I e. Poset

  proof
    cF
    cvv
    wcel
    #
    cI
    cpo
    wcel
    @0
    va
    vb
    vc
    cF
    cI
    cI
    cple
    cfv
    #
    cI
    cvv
    wcel
    @0
    cI
    cF
    cipo
    cfv
    #
    cvv
    ipopos.i
    cF
    cipo
    fvex
    eqeltri
    a1i
    cF
    cI
    cvv
    ipopos.i
    ipobas
    @0
    @1
    eqidd
    @0
    va
    cv
    #
    cF
    wcel
    #
    wa
    @3
    @3
    @1
    wbr
    #
    @3
    @3
    wss
    #
    @3
    ssid
    @0
    @4
    @5
    @6
    wb
    cF
    cI
    @1
    cvv
    @3
    @3
    ipopos.i
    @1
    eqid
    #
    ipole
    3anidm23
    mpbiri
    @0
    @4
    vb
    cv
    #
    cF
    wcel
    #
    w3a
    #
    @3
    @8
    @1
    wbr
    #
    @8
    @3
    @1
    wbr
    #
    wa
    @3
    @8
    wss
    #
    @8
    @3
    wss
    #
    wa
    #
    va
    vb
    weq
    @10
    @11
    @13
    @12
    @14
    cF
    cI
    @1
    cvv
    @3
    @8
    ipopos.i
    @7
    ipole
    #
    @0
    @9
    @4
    @12
    @14
    wb
    cF
    cI
    @1
    cvv
    @8
    @3
    ipopos.i
    @7
    ipole
    3com23
    anbi12d
    @15
    @3
    @8
    @13
    @14
    simpl
    @13
    @14
    simpr
    eqssd
    syl6bi
    @0
    @4
    @9
    vc
    cv
    #
    cF
    wcel
    #
    w3a
    wa
    #
    @13
    @8
    @17
    wss
    #
    wa
    #
    @3
    @17
    wss
    #
    @11
    @8
    @17
    @1
    wbr
    #
    wa
    @3
    @17
    @1
    wbr
    #
    @21
    @22
    wi
    @19
    @3
    @8
    @17
    sstr
    a1i
    @19
    @11
    @13
    @23
    @20
    @0
    @4
    @9
    @11
    @13
    wb
    @18
    @16
    3adant3r3
    @0
    @9
    @18
    @23
    @20
    wb
    @4
    cF
    cI
    @1
    cvv
    @8
    @17
    ipopos.i
    @7
    ipole
    3adant3r1
    anbi12d
    @0
    @4
    @18
    @24
    @22
    wb
    @9
    cF
    cI
    @1
    cvv
    @3
    @17
    ipopos.i
    @7
    ipole
    3adant3r2
    3imtr4d
    isposd
    @0
    wn
    #
    cI
    c0
    cpo
    @25
    cI
    @2
    c0
    ipopos.i
    cF
    cipo
    fvprc
    syl5eq
    0pos
    syl6eqel
    pm2.61i
end
