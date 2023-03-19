include "wcel.mm"
include "cpw.mm"
include "clocfin.mm"
include "cfv.mm"
include "ccref.mm"
include "cpcmp.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "distop.mm"
include "wa.mm"
include "csn.mm"
include "cab.mm"
include "wss.mm"
include "simpr.mm"
include "snelpwi.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "abssi.mm"
include "wb.mm"
include "simpl.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "cbvrexdva.mm"
include "cbvabv.mm"
include "dissnlocfin.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbiri.mm"
include "ad2antrr.mm"
include "elind.mm"
include "simpll.mm"
include "eqcomd.mm"
include "dissnref.mm"
include "syl2anc.mm"
include "breq1.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimiva.mm"
include "unipw.mm"
include "eqcomi.mm"
include "iscref.mm"
include "sylanbrc.mm"
include "ispcmp.mm"
include "sylibr.mm"

theorem dispcmp
  let cV: class V
  let cX: class X
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vx: setvar x


  assert |- ( X e. V -> ~P X e. Paracomp )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    @1
    clocfin
    cfv
    #
    ccref
    wcel
    #
    @1
    cpcmp
    wcel
    @0
    @1
    ctop
    wcel
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cv
    #
    @4
    cref
    wbr
    #
    vz
    @1
    cpw
    #
    @2
    cin
    #
    wrex
    #
    wi
    #
    vy
    @9
    wral
    @3
    cX
    cV
    distop
    @0
    @12
    vy
    @9
    @0
    @4
    @9
    wcel
    #
    wa
    #
    @6
    @11
    @14
    @6
    wa
    #
    vu
    cv
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cX
    wrex
    #
    vu
    cab
    #
    @10
    wcel
    @21
    @4
    cref
    wbr
    #
    @11
    @15
    @9
    @2
    @21
    @0
    @21
    @9
    wcel
    #
    @13
    @6
    @0
    @23
    @21
    @1
    wss
    #
    @20
    vu
    @1
    @19
    @16
    @1
    wcel
    vx
    cX
    @17
    cX
    wcel
    #
    @19
    wa
    @16
    @18
    @1
    @25
    @19
    simpr
    @25
    @18
    @1
    wcel
    @19
    @17
    cX
    snelpwi
    adantr
    eqeltrd
    rexlimiva
    abssi
    @0
    @21
    @2
    wcel
    #
    @23
    @24
    wb
    vz
    vv
    @21
    cV
    cX
    @20
    vv
    cv
    #
    @7
    csn
    #
    wceq
    #
    vz
    cX
    wrex
    vu
    vv
    @16
    @27
    wceq
    #
    @19
    @29
    vx
    vz
    cX
    @30
    @17
    @7
    wceq
    #
    wa
    #
    @16
    @27
    @18
    @28
    @30
    @31
    simpl
    @32
    @17
    @7
    @30
    @31
    simpr
    sneqd
    eqeq12d
    cbvrexdva
    cbvabv
    #
    dissnlocfin
    #
    @21
    @1
    @2
    elpwg
    syl
    mpbiri
    ad2antrr
    @0
    @26
    @13
    @6
    @34
    ad2antrr
    elind
    @15
    @0
    @5
    cX
    wceq
    @22
    @0
    @13
    @6
    simpll
    @15
    cX
    @5
    @14
    @6
    simpr
    eqcomd
    vz
    vv
    @21
    cV
    cX
    @4
    @33
    dissnref
    syl2anc
    @8
    @22
    vz
    @21
    @10
    @7
    @21
    @4
    cref
    breq1
    rspcev
    syl2anc
    ex
    ralrimiva
    vy
    vz
    @2
    @1
    cX
    @1
    cuni
    cX
    cX
    unipw
    eqcomi
    iscref
    sylanbrc
    @1
    ispcmp
    sylibr
end
