include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "cfbas.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "cvv.mm"
include "fbasne0.mm"
include "fvprc.mm"
include "necon1ai.mm"
include "syl.mm"
include "ssfii.mm"
include "fbsspw.mm"
include "sstrd.mm"
include "fieq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "0nelfb.mm"
include "3jca.mm"
include "wa.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "simpr1.mm"
include "fipwss.mm"
include "pwexg.mm"
include "adantr.mm"
include "ssexd.mm"
include "simpr2.mm"
include "biimpa.mm"
include "simpr3.mm"
include "df-nel.mm"
include "sylibr.mm"
include "fiin.mm"
include "ssid.mm"
include "sseq1.mm"
include "rspcev.mm"
include "sylancl.mm"
include "rgen2a.mm"
include "a1i.mm"
include "wb.mm"
include "isfbas2.mm"
include "mpbir2and.mm"
include "ex.mm"
include "impbid2.mm"

theorem fsubbas
  let cA: class A
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( X e. V -> ( ( fi ` A ) e. ( fBas ` X ) <-> ( A C_ ~P X /\ A =/= (/) /\ -. (/) e. ( fi ` A ) ) ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cfi
    cfv
    #
    cX
    cfbas
    cfv
    wcel
    #
    cA
    cX
    cpw
    #
    wss
    #
    cA
    c0
    wne
    #
    c0
    @1
    wcel
    wn
    #
    w3a
    #
    @2
    @4
    @5
    @6
    @2
    cA
    @1
    @3
    @2
    cA
    cvv
    wcel
    #
    cA
    @1
    wss
    @2
    @1
    c0
    wne
    #
    @8
    cX
    @1
    fbasne0
    #
    @8
    @1
    c0
    cA
    cfi
    fvprc
    necon1ai
    syl
    #
    cA
    cvv
    ssfii
    syl
    cX
    @1
    fbsspw
    sstrd
    @2
    @8
    @9
    @5
    @11
    @10
    @8
    @5
    @9
    @8
    cA
    c0
    @1
    c0
    cA
    cvv
    fieq0
    necon3bid
    #
    biimpar
    syl2anc
    cX
    @1
    0nelfb
    3jca
    @0
    @7
    @2
    @0
    @7
    wa
    #
    @2
    @1
    @3
    wss
    #
    @9
    c0
    @1
    wnel
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    vz
    @1
    wrex
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    w3a
    #
    @13
    @4
    @14
    @0
    @4
    @5
    @6
    simpr1
    #
    cA
    cX
    fipwss
    syl
    @13
    @9
    @15
    @22
    @13
    @8
    @5
    @9
    @13
    cA
    @3
    cvv
    @0
    @3
    cvv
    wcel
    @7
    cX
    cV
    pwexg
    adantr
    @24
    ssexd
    @0
    @4
    @5
    @6
    simpr2
    @8
    @5
    @9
    @12
    biimpa
    syl2anc
    @13
    @6
    @15
    @0
    @4
    @5
    @6
    simpr3
    c0
    @1
    df-nel
    sylibr
    @22
    @13
    @21
    vx
    vy
    @1
    @17
    @1
    wcel
    @18
    @1
    wcel
    wa
    @19
    @1
    wcel
    @19
    @19
    wss
    #
    @21
    @17
    @18
    cA
    fiin
    @19
    ssid
    @20
    @25
    vz
    @19
    @1
    @16
    @19
    @19
    sseq1
    rspcev
    sylancl
    rgen2a
    a1i
    3jca
    @0
    @2
    @14
    @23
    wa
    wb
    @7
    vx
    vy
    vz
    cV
    cX
    @1
    isfbas2
    adantr
    mpbir2and
    ex
    impbid2
end
