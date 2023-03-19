include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cdif.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "cnt.mm"
include "cv.mm"
include "ccld.mm"
include "crab.mm"
include "cint.mm"
include "ciin.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "df-rab.mm"
include "cldopn.mm"
include "ad2antrl.mm"
include "sscon.mm"
include "ad2antll.mm"
include "wb.mm"
include "cvv.mm"
include "topopn.mm"
include "difexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "elind.mm"
include "cldss.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "simpl.mm"
include "elin.mm"
include "simplbi.mm"
include "opncld.mm"
include "syl2an.mm"
include "simprbi.mm"
include "adantl.mm"
include "elpwid.mm"
include "difss2d.mm"
include "simplr.mm"
include "ssconb.mm"
include "mpbid.mm"
include "jca.mm"
include "eleq1.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "inteqd.mm"
include "wral.mm"
include "ralrimivw.mm"
include "dfiin2g.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "clsval.mm"
include "ciun.mm"
include "uniiun.mm"
include "difeq2i.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "0opn.mm"
include "0elpw.mm"
include "ne0i.mm"
include "iindif2.mm"
include "3eqtr4d.mm"
include "difssd.mm"
include "ntrval.mm"
include "sylan2.mm"
include "difeq2d.mm"

theorem clsval2
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` S ) = ( X \ ( ( int ` J ) ` ( X \ S ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cX
    cJ
    cX
    cS
    cdif
    #
    cpw
    #
    cin
    #
    cuni
    #
    cdif
    #
    cX
    @4
    cJ
    cnt
    cfv
    cfv
    #
    cdif
    @2
    cS
    vz
    cv
    #
    wss
    #
    vz
    cJ
    ccld
    cfv
    #
    crab
    #
    cint
    #
    vx
    @6
    cX
    vx
    cv
    #
    cdif
    #
    ciin
    #
    @3
    @8
    @2
    @14
    @10
    @16
    wceq
    #
    vx
    @6
    wrex
    #
    vz
    cab
    #
    cint
    #
    @17
    @2
    @13
    @20
    @2
    @13
    @10
    @12
    wcel
    #
    @11
    wa
    #
    vz
    cab
    @20
    @11
    vz
    @12
    df-rab
    @2
    @23
    @19
    vz
    @2
    @23
    @19
    @2
    @23
    @19
    @2
    @23
    wa
    #
    cX
    @10
    cdif
    #
    @6
    wcel
    @10
    cX
    @25
    cdif
    #
    wceq
    #
    @19
    @24
    cJ
    @5
    @25
    @22
    @25
    cJ
    wcel
    @2
    @11
    @10
    cJ
    cX
    clscld.1
    cldopn
    ad2antrl
    @24
    @25
    @5
    wcel
    #
    @25
    @4
    wss
    #
    @11
    @29
    @2
    @22
    cS
    @10
    cX
    sscon
    ad2antll
    @0
    @28
    @29
    wb
    #
    @1
    @23
    @0
    cX
    cJ
    wcel
    #
    @25
    cvv
    wcel
    @30
    cJ
    cX
    clscld.1
    topopn
    #
    cX
    @10
    cJ
    difexg
    @25
    @4
    cvv
    elpwg
    3syl
    ad2antrr
    mpbird
    elind
    @24
    @26
    @10
    @24
    @10
    cX
    wss
    #
    @26
    @10
    wceq
    @22
    @33
    @2
    @11
    @10
    cJ
    cX
    clscld.1
    cldss
    ad2antrl
    @10
    cX
    dfss4
    sylib
    eqcomd
    @18
    @27
    vx
    @25
    @6
    @15
    @25
    wceq
    @16
    @26
    @10
    @15
    @25
    cX
    difeq2
    eqeq2d
    rspcev
    syl2anc
    ex
    @2
    @18
    @23
    vx
    @6
    @2
    @15
    @6
    wcel
    #
    wa
    #
    @23
    @18
    @16
    @12
    wcel
    #
    cS
    @16
    wss
    #
    wa
    @35
    @36
    @37
    @2
    @0
    @15
    cJ
    wcel
    #
    @36
    @34
    @0
    @1
    simpl
    @34
    @38
    @15
    @5
    wcel
    #
    @15
    cJ
    @5
    elin
    #
    simplbi
    @15
    cJ
    cX
    clscld.1
    opncld
    syl2an
    @35
    @15
    @4
    wss
    #
    @37
    @35
    @15
    @4
    @34
    @39
    @2
    @34
    @38
    @39
    @40
    simprbi
    adantl
    elpwid
    #
    @35
    @15
    cX
    wss
    @1
    @41
    @37
    wb
    @35
    @15
    cX
    cS
    @42
    difss2d
    @0
    @1
    @34
    simplr
    @15
    cS
    cX
    ssconb
    syl2anc
    mpbid
    jca
    @18
    @22
    @36
    @11
    @37
    @10
    @16
    @12
    eleq1
    @10
    @16
    cS
    sseq2
    anbi12d
    syl5ibrcom
    rexlimdva
    impbid
    abbidv
    syl5eq
    inteqd
    @0
    @17
    @21
    wceq
    #
    @1
    @0
    @31
    @16
    cvv
    wcel
    #
    vx
    @6
    wral
    @43
    @32
    @31
    @44
    vx
    @6
    cX
    @15
    cJ
    difexg
    ralrimivw
    vx
    vz
    @6
    @16
    cvv
    dfiin2g
    3syl
    adantr
    eqtr4d
    vz
    cS
    cJ
    cX
    clscld.1
    clsval
    @2
    @8
    cX
    vx
    @6
    @15
    ciun
    #
    cdif
    #
    @17
    @8
    @46
    wceq
    @2
    @7
    @45
    cX
    vx
    @6
    uniiun
    difeq2i
    a1i
    @2
    c0
    @6
    wcel
    @6
    c0
    wne
    @17
    @46
    wceq
    @2
    cJ
    @5
    c0
    @0
    c0
    cJ
    wcel
    @1
    cJ
    0opn
    adantr
    c0
    @5
    wcel
    @2
    @4
    0elpw
    a1i
    elind
    @6
    c0
    ne0i
    vx
    @6
    cX
    @15
    iindif2
    3syl
    eqtr4d
    3eqtr4d
    @2
    @9
    @7
    cX
    @1
    @0
    @4
    cX
    wss
    @9
    @7
    wceq
    @1
    cX
    cS
    difssd
    @4
    cJ
    cX
    clscld.1
    ntrval
    sylan2
    difeq2d
    eqtr4d
end
