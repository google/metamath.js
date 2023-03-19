include "cen.mm"
include "wbr.mm"
include "cfin4.mm"
include "wcel.mm"
include "wi.mm"
include "ensym.mm"
include "cv.mm"
include "wpss.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wf1o.mm"
include "bren.mm"
include "cima.mm"
include "simpr.mm"
include "wf1.mm"
include "wss.mm"
include "wb.mm"
include "f1of1.mm"
include "pssss.mm"
include "ssid.mm"
include "jctir.mm"
include "f1imapss.mm"
include "syl2an.mm"
include "mpbird.mm"
include "wceq.mm"
include "cdm.mm"
include "crn.mm"
include "imadmrn.mm"
include "f1odm.mm"
include "imaeq2d.mm"
include "dff1o5.mm"
include "simprbi.mm"
include "3eqtr3a.mm"
include "adantr.mm"
include "psseq2d.mm"
include "mpbid.mm"
include "adantrr.mm"
include "vex.mm"
include "f1imaen.mm"
include "simprr.mm"
include "entr.mm"
include "syl2anc.mm"
include "cvv.mm"
include "f1oen3g.mm"
include "mpan.mm"
include "fin4i.mm"
include "ex.mm"
include "exlimdv.mm"
include "con2d.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "relen.mm"
include "brrelexi.mm"
include "isfin4.mm"
include "syl.mm"
include "sylibrd.mm"

theorem fin4en1
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x


  assert |- ( A ~~ B -> ( A e. Fin4 -> B e. Fin4 ) )

  proof
    cA
    cB
    cen
    wbr
    cB
    cA
    cen
    wbr
    #
    cA
    cfin4
    wcel
    #
    cB
    cfin4
    wcel
    #
    wi
    cA
    cB
    ensym
    @0
    @1
    vx
    cv
    #
    cB
    wpss
    #
    @3
    cB
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    wn
    #
    @2
    @0
    cB
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @1
    @8
    wi
    #
    cB
    cA
    vf
    bren
    @10
    @11
    vf
    @10
    @7
    @1
    @10
    @6
    @1
    wn
    #
    vx
    @10
    @6
    @12
    @10
    @6
    wa
    #
    @9
    @3
    cima
    #
    cA
    wpss
    #
    @14
    cA
    cen
    wbr
    #
    @12
    @10
    @4
    @15
    @5
    @10
    @4
    wa
    #
    @14
    @9
    cB
    cima
    #
    wpss
    #
    @15
    @17
    @19
    @4
    @10
    @4
    simpr
    @10
    cB
    cA
    @9
    wf1
    #
    @3
    cB
    wss
    #
    cB
    cB
    wss
    #
    wa
    @19
    @4
    wb
    @4
    cB
    cA
    @9
    f1of1
    #
    @4
    @21
    @22
    @3
    cB
    pssss
    #
    cB
    ssid
    jctir
    cB
    cA
    @3
    cB
    @9
    f1imapss
    syl2an
    mpbird
    @17
    @18
    cA
    @14
    @10
    @18
    cA
    wceq
    @4
    @10
    @9
    @9
    cdm
    #
    cima
    @9
    crn
    #
    @18
    cA
    @9
    imadmrn
    @10
    @25
    cB
    @9
    cB
    cA
    @9
    f1odm
    imaeq2d
    @10
    @20
    @26
    cA
    wceq
    cB
    cA
    @9
    dff1o5
    simprbi
    3eqtr3a
    adantr
    psseq2d
    mpbid
    adantrr
    @13
    @14
    cB
    cen
    wbr
    #
    @0
    @16
    @13
    @14
    @3
    cen
    wbr
    #
    @5
    @27
    @10
    @4
    @28
    @5
    @10
    @20
    @21
    @28
    @4
    @23
    @24
    cB
    cA
    @3
    @9
    vx
    vex
    f1imaen
    syl2an
    adantrr
    @10
    @4
    @5
    simprr
    @14
    @3
    cB
    entr
    syl2anc
    @10
    @0
    @6
    @9
    cvv
    wcel
    @10
    @0
    vf
    vex
    cB
    cA
    @9
    cvv
    f1oen3g
    mpan
    adantr
    @14
    cB
    cA
    entr
    syl2anc
    cA
    @14
    fin4i
    syl2anc
    ex
    exlimdv
    con2d
    exlimiv
    sylbi
    @0
    cB
    cvv
    wcel
    @2
    @8
    wb
    cB
    cA
    cen
    relen
    brrelexi
    vx
    cB
    cvv
    isfin4
    syl
    sylibrd
    syl
end
