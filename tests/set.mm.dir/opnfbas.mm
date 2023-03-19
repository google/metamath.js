include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "cfbas.mm"
include "cfv.mm"
include "cpw.mm"
include "wnel.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ssrab2.mm"
include "cuni.mm"
include "eqimss2i.mm"
include "sspwuni.mm"
include "mpbir.mm"
include "sstri.mm"
include "a1i.mm"
include "wa.mm"
include "topopn.mm"
include "anim1i.mm"
include "3adant3.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "syl.mm"
include "wn.mm"
include "ss0.mm"
include "necon3ai.mm"
include "3ad2ant3.mm"
include "intnand.mm"
include "df-nel.mm"
include "notbii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "anbi12i.mm"
include "simpl.mm"
include "simprll.mm"
include "simprrl.mm"
include "inopn.mm"
include "syl3anc.mm"
include "ssin.mm"
include "biimpi.mm"
include "ad2ant2l.mm"
include "adantl.mm"
include "jca.mm"
include "3ad2antl1.mm"
include "ssid.mm"
include "sseq1.mm"
include "rspcev.mm"
include "sylancl.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimivv.mm"
include "3jca.mm"
include "wb.mm"
include "isfbas2.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem opnfbas
  let vx: setvar x
  let cS: class S
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  assume opnfbas.1: |- X = U. J

  disjoint J x
  disjoint S x
  disjoint X x
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint J r
  disjoint s t
  disjoint s x
  disjoint J s
  disjoint t x
  disjoint J t
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint X r
  disjoint X s
  disjoint X t
  assert |- ( ( J e. Top /\ S C_ X /\ S =/= (/) ) -> { x e. J | S C_ x } e. ( fBas ` X ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cS
    vx
    cv
    #
    wss
    #
    vx
    cJ
    crab
    #
    cX
    cfbas
    cfv
    wcel
    #
    @6
    cX
    cpw
    #
    wss
    #
    @6
    c0
    wne
    #
    c0
    @6
    wnel
    #
    vt
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cin
    #
    wss
    #
    vt
    @6
    wrex
    #
    vs
    @6
    wral
    vr
    @6
    wral
    #
    w3a
    #
    @9
    @3
    @6
    cJ
    @8
    @5
    vx
    cJ
    ssrab2
    cJ
    @8
    wss
    cJ
    cuni
    #
    cX
    wss
    cX
    @20
    opnfbas.1
    eqimss2i
    cJ
    cX
    sspwuni
    mpbir
    sstri
    a1i
    @3
    @10
    @11
    @18
    @3
    cX
    @6
    wcel
    #
    @10
    @3
    cX
    cJ
    wcel
    #
    @1
    wa
    #
    @21
    @0
    @1
    @23
    @2
    @0
    @22
    @1
    cJ
    cX
    opnfbas.1
    topopn
    #
    anim1i
    3adant3
    @5
    @1
    vx
    cX
    cJ
    @4
    cX
    cS
    sseq2
    elrab
    sylibr
    @6
    cX
    ne0i
    syl
    @3
    c0
    cJ
    wcel
    #
    cS
    c0
    wss
    #
    wa
    #
    wn
    #
    @11
    @3
    @26
    @25
    @2
    @0
    @26
    wn
    @1
    @26
    cS
    c0
    cS
    ss0
    necon3ai
    3ad2ant3
    intnand
    @11
    c0
    @6
    wcel
    #
    wn
    @28
    c0
    @6
    df-nel
    @29
    @27
    @5
    @26
    vx
    c0
    cJ
    @4
    c0
    cS
    sseq2
    elrab
    notbii
    bitr2i
    sylib
    @3
    @17
    vr
    vs
    @6
    @6
    @13
    @6
    wcel
    #
    @14
    @6
    wcel
    #
    wa
    @13
    cJ
    wcel
    #
    cS
    @13
    wss
    #
    wa
    #
    @14
    cJ
    wcel
    #
    cS
    @14
    wss
    #
    wa
    #
    wa
    #
    @3
    @17
    @30
    @34
    @31
    @37
    @5
    @33
    vx
    @13
    cJ
    @4
    @13
    cS
    sseq2
    elrab
    @5
    @36
    vx
    @14
    cJ
    @4
    @14
    cS
    sseq2
    elrab
    anbi12i
    @3
    @38
    @17
    @3
    @38
    wa
    #
    @15
    @6
    wcel
    #
    @15
    @15
    wss
    #
    @17
    @39
    @15
    cJ
    wcel
    #
    cS
    @15
    wss
    #
    wa
    #
    @40
    @0
    @1
    @38
    @44
    @2
    @0
    @38
    wa
    #
    @42
    @43
    @45
    @0
    @32
    @35
    @42
    @0
    @38
    simpl
    @0
    @32
    @33
    @37
    simprll
    @0
    @34
    @35
    @36
    simprrl
    @13
    @14
    cJ
    inopn
    syl3anc
    @38
    @43
    @0
    @33
    @36
    @43
    @32
    @35
    @33
    @36
    wa
    @43
    cS
    @13
    @14
    ssin
    biimpi
    ad2ant2l
    adantl
    jca
    3ad2antl1
    @5
    @43
    vx
    @15
    cJ
    @4
    @15
    cS
    sseq2
    elrab
    sylibr
    @15
    ssid
    @16
    @41
    vt
    @15
    @6
    @12
    @15
    @15
    sseq1
    rspcev
    sylancl
    ex
    syl5bi
    ralrimivv
    3jca
    @0
    @1
    @7
    @9
    @19
    wa
    wb
    #
    @2
    @0
    @22
    @46
    @24
    vr
    vs
    vt
    cJ
    cX
    @6
    isfbas2
    syl
    3ad2ant1
    mpbir2and
end
