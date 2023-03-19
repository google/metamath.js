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
include "simpl2.mm"
include "filunibas.mm"
include "syl.mm"
include "flimfil.mm"
include "eqtr3d.mm"
include "eleqtrrd.mm"
include "ctop.mm"
include "simpl1.mm"
include "topontop.mm"
include "flimtop.mm"
include "toponuni.mm"
include "simpl3.mm"
include "topssnei.mm"
include "syl31anc.mm"
include "flimneiss.mm"
include "sstrd.mm"
include "wb.mm"
include "elflim.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem flimss1
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cG: class G


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ J C_ K ) -> ( K fLim F ) C_ ( J fLim F ) )

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
    cJ
    cK
    wss
    #
    w3a
    #
    vx
    cK
    cF
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
    #
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
    cK
    cuni
    #
    cX
    @7
    @6
    @14
    wcel
    @3
    @6
    cF
    cK
    @14
    @14
    eqid
    #
    flimelbas
    adantl
    @9
    cF
    cuni
    #
    cX
    @14
    @9
    @1
    @16
    cX
    wceq
    @0
    @1
    @2
    @7
    simpl2
    #
    cF
    cX
    filunibas
    syl
    @9
    cF
    @14
    cfil
    cfv
    wcel
    #
    @16
    @14
    wceq
    @7
    @18
    @3
    @6
    cF
    cK
    @14
    @15
    flimfil
    adantl
    cF
    @14
    filunibas
    syl
    eqtr3d
    #
    eleqtrrd
    @9
    @12
    @11
    cK
    cnei
    cfv
    cfv
    #
    cF
    @9
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cJ
    cuni
    #
    @14
    wceq
    @2
    @12
    @20
    wss
    @9
    @0
    @21
    @0
    @1
    @2
    @7
    simpl1
    #
    cX
    cJ
    topontop
    syl
    @7
    @22
    @3
    @6
    cF
    cK
    flimtop
    adantl
    @9
    cX
    @23
    @14
    @9
    @0
    cX
    @23
    wceq
    @24
    cX
    cJ
    toponuni
    syl
    @19
    eqtr3d
    @0
    @1
    @2
    @7
    simpl3
    @11
    cJ
    cK
    @23
    @14
    @23
    eqid
    @15
    topssnei
    syl31anc
    @7
    @20
    cF
    wss
    @3
    @6
    cF
    cK
    flimneiss
    adantl
    sstrd
    @9
    @0
    @1
    @8
    @10
    @13
    wa
    wb
    @24
    @17
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
