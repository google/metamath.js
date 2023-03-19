include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "cab.mm"
include "elin.mm"
include "wceq.mm"
include "wb.mm"
include "crn.mm"
include "wf1o.mm"
include "wfo.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "eleq2d.mm"
include "3syl.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "cvv.mm"
include "fvex.mm"
include "vex.mm"
include "eliniseg.mm"
include "mp1i.mm"
include "anbi12d.mm"
include "adantr.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "adantl.mm"
include "wi.mm"
include "isorel.mm"
include "syl.mm"
include "fnbrfvb.mm"
include "bicomd.mm"
include "sylan.mm"
include "adantrr.mm"
include "ancom.mm"
include "breq1.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "exp32.mm"
include "com23.mm"
include "imp.mm"
include "pm5.32d.mm"
include "bitrd.mm"
include "rexbidv2.mm"
include "r19.41v.mm"
include "bitr4d.mm"
include "abbi2dv.mm"
include "dfima2.mm"
include "syl6reqr.mm"

theorem isoini
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( H Isom R , S ( A , B ) /\ D e. A ) -> ( H " ( A i^i ( `' R " { D } ) ) ) = ( B i^i ( `' S " { ( H ` D ) } ) ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cD
    cA
    wcel
    #
    wa
    #
    cB
    cS
    ccnv
    cD
    cH
    cfv
    #
    csn
    cima
    #
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    wbr
    #
    vx
    cA
    cR
    ccnv
    cD
    csn
    cima
    #
    cin
    #
    wrex
    #
    vy
    cab
    cH
    @10
    cima
    @2
    @11
    vy
    @5
    @7
    @5
    wcel
    @7
    cB
    wcel
    #
    @7
    @4
    wcel
    #
    wa
    #
    @2
    @11
    @7
    cB
    @4
    elin
    @2
    @14
    @6
    cH
    cfv
    #
    @7
    wceq
    #
    vx
    cA
    wrex
    #
    @7
    @3
    cS
    wbr
    #
    wa
    #
    @11
    @0
    @14
    @19
    wb
    @1
    @0
    @12
    @17
    @13
    @18
    @0
    @7
    cH
    crn
    #
    wcel
    #
    @12
    @17
    @0
    cA
    cB
    cH
    wf1o
    #
    cA
    cB
    cH
    wfo
    #
    @21
    @12
    wb
    cA
    cB
    cR
    cS
    cH
    isof1o
    #
    cA
    cB
    cH
    f1ofo
    @23
    @20
    cB
    @7
    cA
    cB
    cH
    forn
    eleq2d
    3syl
    @0
    @22
    cH
    cA
    wfn
    #
    @21
    @17
    wb
    @24
    cA
    cB
    cH
    f1ofn
    #
    vx
    cA
    @7
    cH
    fvelrnb
    3syl
    bitr3d
    @3
    cvv
    wcel
    @13
    @18
    wb
    @0
    cD
    cH
    fvex
    cS
    @3
    @7
    cvv
    vy
    vex
    eliniseg
    mp1i
    anbi12d
    adantr
    @2
    @11
    @16
    @18
    wa
    #
    vx
    cA
    wrex
    @19
    @2
    @8
    @27
    vx
    @10
    cA
    @2
    @6
    @10
    wcel
    #
    @8
    wa
    #
    @6
    cA
    wcel
    #
    @6
    cD
    cR
    wbr
    #
    @8
    wa
    #
    wa
    #
    @30
    @27
    wa
    @1
    @29
    @33
    wb
    @0
    @1
    @29
    @30
    @31
    wa
    #
    @8
    wa
    @33
    @1
    @28
    @34
    @8
    @28
    @30
    @6
    @9
    wcel
    #
    wa
    @1
    @34
    @6
    cA
    @9
    elin
    @1
    @35
    @31
    @30
    cR
    cD
    @6
    cA
    vx
    vex
    eliniseg
    anbi2d
    syl5bb
    anbi1d
    @30
    @31
    @8
    anass
    syl6bb
    adantl
    @2
    @30
    @32
    @27
    @0
    @1
    @30
    @32
    @27
    wb
    #
    wi
    @0
    @30
    @1
    @36
    @0
    @30
    @1
    @36
    @0
    @30
    @1
    wa
    wa
    #
    @32
    @15
    @3
    cS
    wbr
    #
    @16
    wa
    #
    @27
    @37
    @31
    @38
    @8
    @16
    cA
    cB
    @6
    cD
    cR
    cS
    cH
    isorel
    @0
    @30
    @8
    @16
    wb
    #
    @1
    @0
    @25
    @30
    @40
    @0
    @22
    @25
    @24
    @26
    syl
    @25
    @30
    wa
    @16
    @8
    cA
    @6
    @7
    cH
    fnbrfvb
    bicomd
    sylan
    adantrr
    anbi12d
    @39
    @16
    @38
    wa
    @27
    @38
    @16
    ancom
    @16
    @38
    @18
    @15
    @7
    @3
    cS
    breq1
    pm5.32i
    bitri
    syl6bb
    exp32
    com23
    imp
    pm5.32d
    bitrd
    rexbidv2
    @16
    @18
    vx
    cA
    r19.41v
    syl6bb
    bitr4d
    syl5bb
    abbi2dv
    vx
    vy
    cH
    @10
    dfima2
    syl6reqr
end
