include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cvv.mm"
include "difexg.mm"
include "enrefg.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "wne.mm"
include "wa.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "simpl1.mm"
include "4syl.mm"
include "dif32.mm"
include "syl6breq.mm"
include "simpl3.mm"
include "simpl2.mm"
include "en2sn.mm"
include "syl2anc.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "unen.mm"
include "syl22anc.mm"
include "simpr.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "difsnid.mm"
include "3brtr3d.mm"
include "pm2.61dane.mm"

theorem difsnen
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X


  assert |- ( ( X e. V /\ A e. X /\ B e. X ) -> ( X \ { A } ) ~~ ( X \ { B } ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cX
    cA
    csn
    #
    cdif
    #
    cX
    cB
    csn
    #
    cdif
    #
    cen
    wbr
    #
    cA
    cB
    @3
    cA
    cB
    wceq
    #
    @8
    @3
    @5
    @5
    cen
    wbr
    #
    @9
    @8
    @0
    @1
    @10
    @2
    @0
    @5
    cvv
    wcel
    #
    @10
    cX
    @4
    cV
    difexg
    #
    @5
    cvv
    enrefg
    syl
    3ad2ant1
    @9
    @5
    @7
    @5
    cen
    @9
    @4
    @6
    cX
    cA
    cB
    sneq
    difeq2d
    breq2d
    syl5ibcom
    imp
    @3
    cA
    cB
    wne
    #
    wa
    #
    @5
    @6
    cdif
    #
    @6
    cun
    #
    @7
    @4
    cdif
    #
    @4
    cun
    #
    @5
    @7
    cen
    @14
    @15
    @17
    cen
    wbr
    @6
    @4
    cen
    wbr
    #
    @15
    @6
    cin
    #
    c0
    wceq
    #
    @17
    @4
    cin
    #
    c0
    wceq
    #
    @16
    @18
    cen
    wbr
    @14
    @15
    @15
    @17
    cen
    @14
    @0
    @11
    @15
    cvv
    wcel
    @15
    @15
    cen
    wbr
    @0
    @1
    @2
    @13
    simpl1
    @12
    @5
    @6
    cvv
    difexg
    @15
    cvv
    enrefg
    4syl
    cX
    @4
    @6
    dif32
    syl6breq
    @14
    @2
    @1
    @19
    @0
    @1
    @2
    @13
    simpl3
    #
    @0
    @1
    @2
    @13
    simpl2
    #
    cB
    cA
    cX
    cX
    en2sn
    syl2anc
    @21
    @14
    @20
    @6
    @15
    cin
    c0
    @15
    @6
    incom
    @6
    @5
    disjdif
    eqtri
    a1i
    @23
    @14
    @22
    @4
    @17
    cin
    c0
    @17
    @4
    incom
    @4
    @7
    disjdif
    eqtri
    a1i
    @15
    @17
    @6
    @4
    unen
    syl22anc
    @14
    cB
    @5
    wcel
    #
    @16
    @5
    wceq
    @14
    @2
    cB
    cA
    wne
    @26
    @24
    @14
    cA
    cB
    @3
    @13
    simpr
    #
    necomd
    cB
    cX
    cA
    eldifsn
    sylanbrc
    @5
    cB
    difsnid
    syl
    @14
    cA
    @7
    wcel
    #
    @18
    @7
    wceq
    @14
    @1
    @13
    @28
    @25
    @27
    cA
    cX
    cB
    eldifsn
    sylanbrc
    @7
    cA
    difsnid
    syl
    3brtr3d
    pm2.61dane
end
