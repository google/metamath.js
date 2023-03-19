include "cina.mm"
include "cvv.mm"
include "wnel.mm"
include "cuni.mm"
include "con0.mm"
include "wceq.mm"
include "wss.mm"
include "word.mm"
include "cv.mm"
include "wcel.mm"
include "cwina.mm"
include "inawina.mm"
include "winaon.mm"
include "syl.mm"
include "ssriv.mm"
include "ssorduni.mm"
include "ordsson.mm"
include "mp2b.mm"
include "wrex.mm"
include "ctsk.mm"
include "vex.mm"
include "grothtsk.mm"
include "eleqtrri.mm"
include "eluni2.mm"
include "mpbi.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "tskcard.mm"
include "sylan2.mm"
include "adantl.mm"
include "csdm.mm"
include "wbr.mm"
include "tsksdom.mm"
include "cdm.mm"
include "wb.mm"
include "tskwe2.mm"
include "adantr.mm"
include "cardsdomel.mm"
include "mpbid.mm"
include "eleq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "mpi.mm"
include "sylibr.mm"
include "eqssi.mm"
include "ssonprc.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem inaprc
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Inacc e/ _V

  proof
    cina
    cvv
    wnel
    #
    cina
    cuni
    #
    con0
    wceq
    #
    @1
    con0
    cina
    con0
    wss
    #
    @1
    word
    @1
    con0
    wss
    vx
    cina
    con0
    vx
    cv
    #
    cina
    wcel
    @4
    cwina
    wcel
    @4
    con0
    wcel
    @4
    inawina
    @4
    winaon
    syl
    ssriv
    #
    cina
    ssorduni
    @1
    ordsson
    mp2b
    vy
    con0
    @1
    vy
    cv
    #
    con0
    wcel
    #
    @6
    vz
    cv
    #
    wcel
    #
    vz
    cina
    wrex
    #
    @6
    @1
    wcel
    @7
    @6
    vw
    cv
    #
    wcel
    #
    vw
    ctsk
    wrex
    #
    @10
    @6
    ctsk
    cuni
    #
    wcel
    @13
    @6
    cvv
    @14
    vy
    vex
    grothtsk
    eleqtrri
    vw
    @6
    ctsk
    eluni2
    mpbi
    @7
    @12
    @10
    vw
    ctsk
    @7
    @11
    ctsk
    wcel
    #
    @12
    wa
    #
    wa
    #
    @11
    ccrd
    cfv
    #
    cina
    wcel
    #
    @6
    @18
    wcel
    #
    @10
    @16
    @19
    @7
    @12
    @15
    @11
    c0
    wne
    @19
    @11
    @6
    ne0i
    @11
    tskcard
    sylan2
    adantl
    @17
    @6
    @11
    csdm
    wbr
    #
    @20
    @16
    @21
    @7
    @6
    @11
    tsksdom
    adantl
    @16
    @7
    @11
    ccrd
    cdm
    wcel
    #
    @21
    @20
    wb
    @15
    @22
    @12
    @11
    tskwe2
    adantr
    @6
    @11
    cardsdomel
    sylan2
    mpbid
    @9
    @20
    vz
    @18
    cina
    @8
    @18
    @6
    eleq2
    rspcev
    syl2anc
    rexlimdvaa
    mpi
    vz
    @6
    cina
    eluni2
    sylibr
    ssriv
    eqssi
    @3
    @0
    @2
    wb
    @5
    cina
    ssonprc
    ax-mp
    mpbir
end
