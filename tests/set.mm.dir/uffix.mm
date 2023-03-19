include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfbas.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "cfg.mm"
include "co.mm"
include "wceq.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "snssi.mm"
include "adantl.mm"
include "snnzg.mm"
include "simpl.mm"
include "snfbas.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wb.mm"
include "selpw.mm"
include "a1i.mm"
include "snex.mm"
include "snid.mm"
include "sseq1.mm"
include "rspcev.mm"
include "sylancr.mm"
include "cint.mm"
include "wi.mm"
include "intss1.mm"
include "sstr2.mm"
include "syl.mm"
include "snidg.mm"
include "intsn.mm"
include "syl6eleqr.mm"
include "ssel.mm"
include "syl5com.mm"
include "sylan9r.mm"
include "rexlimdva.mm"
include "impbid2.mm"
include "anbi12d.mm"
include "eleq2.mm"
include "elrab.mm"
include "elfg.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "jca.mm"

theorem uffix
  let vx: setvar x
  let cA: class A
  let cV: class V
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint X x
  disjoint V x
  disjoint x y
  disjoint A y
  disjoint X y
  disjoint V y
  assert |- ( ( X e. V /\ A e. X ) -> ( { { A } } e. ( fBas ` X ) /\ { x e. ~P X | A e. x } = ( X filGen { { A } } ) ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    csn
    #
    csn
    #
    cX
    cfbas
    cfv
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    cX
    @4
    cfg
    co
    #
    wceq
    @2
    @3
    cX
    wss
    #
    @3
    c0
    wne
    #
    @0
    @5
    @1
    @11
    @0
    cA
    cX
    snssi
    adantl
    @1
    @12
    @0
    cA
    cX
    snnzg
    adantl
    @0
    @1
    simpl
    @3
    cX
    cV
    snfbas
    syl3anc
    #
    @2
    vy
    @9
    @10
    @2
    vy
    cv
    #
    @8
    wcel
    #
    cA
    @14
    wcel
    #
    wa
    #
    @14
    cX
    wss
    #
    @6
    @14
    wss
    #
    vx
    @4
    wrex
    #
    wa
    #
    @14
    @9
    wcel
    #
    @14
    @10
    wcel
    #
    @2
    @15
    @18
    @16
    @20
    @15
    @18
    wb
    @2
    vy
    cX
    selpw
    a1i
    @2
    @16
    @20
    @16
    @3
    @4
    wcel
    @3
    @14
    wss
    #
    @20
    @3
    cA
    snex
    #
    snid
    cA
    @14
    snssi
    @19
    @24
    vx
    @3
    @4
    @6
    @3
    @14
    sseq1
    rspcev
    sylancr
    @2
    @19
    @16
    vx
    @4
    @6
    @4
    wcel
    #
    @19
    @4
    cint
    #
    @14
    wss
    #
    @2
    @16
    @26
    @27
    @6
    wss
    @19
    @28
    wi
    @6
    @4
    intss1
    @27
    @6
    @14
    sstr2
    syl
    @2
    cA
    @27
    wcel
    @28
    @16
    @2
    cA
    @3
    @27
    @1
    cA
    @3
    wcel
    @0
    cA
    cX
    snidg
    adantl
    @3
    @25
    intsn
    syl6eleqr
    @27
    @14
    cA
    ssel
    syl5com
    sylan9r
    rexlimdva
    impbid2
    anbi12d
    @22
    @17
    wb
    @2
    @7
    @16
    vx
    @14
    @8
    @6
    @14
    cA
    eleq2
    elrab
    a1i
    @2
    @5
    @23
    @21
    wb
    @13
    vx
    @14
    @4
    cX
    elfg
    syl
    3bitr4d
    eqrdv
    jca
end
