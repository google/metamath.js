include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wss.mm"
include "w3a.mm"
include "cflim.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cuni.mm"
include "eqid.mm"
include "flimelbas.mm"
include "adantl.mm"
include "wceq.mm"
include "simpl1.mm"
include "toponuni.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "flimneiss.mm"
include "simpl3.mm"
include "sstrd.mm"
include "wb.mm"
include "simpl2.mm"
include "elflim.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem flimss2
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cK: class K


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ G C_ F ) -> ( J fLim G ) C_ ( J fLim F ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    cG
    cF
    wss
    #
    w3a
    #
    vx
    cJ
    cG
    cflim
    co
    #
    cJ
    cF
    cflim
    co
    #
    @3
    vx
    cv
    #
    @4
    wcel
    #
    @6
    @5
    wcel
    #
    @3
    @7
    wa
    #
    @8
    @6
    cX
    wcel
    #
    @6
    csn
    cJ
    cnei
    cfv
    cfv
    #
    cF
    wss
    #
    @9
    @6
    cJ
    cuni
    #
    cX
    @7
    @6
    @13
    wcel
    @3
    @6
    cG
    cJ
    @13
    @13
    eqid
    flimelbas
    adantl
    @9
    @0
    cX
    @13
    wceq
    @0
    @1
    @2
    @7
    simpl1
    #
    cX
    cJ
    toponuni
    syl
    eleqtrrd
    @9
    @11
    cG
    cF
    @7
    @11
    cG
    wss
    @3
    @6
    cG
    cJ
    flimneiss
    adantl
    @0
    @1
    @2
    @7
    simpl3
    sstrd
    @9
    @0
    @1
    @8
    @10
    @12
    wa
    wb
    @14
    @0
    @1
    @2
    @7
    simpl2
    @6
    cF
    cJ
    cX
    elflim
    syl2anc
    mpbir2and
    ex
    ssrdv
end
