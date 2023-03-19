include "cmbf.mm"
include "wcel.mm"
include "wf.mm"
include "cc.mm"
include "wss.mm"
include "w3a.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "crest.mm"
include "co.mm"
include "eleq2i.mm"
include "ctop.mm"
include "cvv.mm"
include "wb.mm"
include "cnfldtop.mm"
include "simp3.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "elrest.mm"
include "sylancr.mm"
include "syl5bb.mm"
include "wa.mm"
include "wfun.mm"
include "simpl2.mm"
include "ffun.mm"
include "inpreima.mm"
include "3syl.mm"
include "mbfimaopn.mm"
include "3ad2antl1.mm"
include "fimacnv.mm"
include "fdm.mm"
include "eqtr4d.mm"
include "syl.mm"
include "simpl1.mm"
include "mbfdm.mm"
include "eqeltrd.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem mbfimaopn2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cG: class G
  assume mbfimaopn.1: |- J = ( TopOpen ` CCfld )
  assume mbfimaopn2.2: |- K = ( J |`t B )


  assert |- ( ( ( F e. MblFn /\ F : A --> B /\ B C_ CC ) /\ C e. K ) -> ( `' F " C ) e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cB
    cc
    wss
    #
    w3a
    #
    cC
    cK
    wcel
    #
    cF
    ccnv
    #
    cC
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    @3
    @4
    cC
    vu
    cv
    #
    cB
    cin
    #
    wceq
    #
    vu
    cJ
    wrex
    #
    @8
    @4
    cC
    cJ
    cB
    crest
    co
    #
    wcel
    #
    @3
    @12
    cK
    @13
    cC
    mbfimaopn2.2
    eleq2i
    @3
    cJ
    ctop
    wcel
    cB
    cvv
    wcel
    #
    @14
    @12
    wb
    cJ
    mbfimaopn.1
    cnfldtop
    @3
    @2
    cc
    cvv
    wcel
    @15
    @0
    @1
    @2
    simp3
    cnex
    cB
    cc
    cvv
    ssexg
    sylancl
    vu
    cC
    cB
    cJ
    ctop
    cvv
    elrest
    sylancr
    syl5bb
    @3
    @11
    @8
    vu
    cJ
    @3
    @9
    cJ
    wcel
    #
    wa
    #
    @8
    @11
    @5
    @10
    cima
    #
    @7
    wcel
    @17
    @18
    @5
    @9
    cima
    #
    @5
    cB
    cima
    #
    cin
    #
    @7
    @17
    @1
    cF
    wfun
    @18
    @21
    wceq
    @0
    @1
    @2
    @16
    simpl2
    #
    cA
    cB
    cF
    ffun
    @9
    cB
    cF
    inpreima
    3syl
    @17
    @19
    @7
    wcel
    #
    @20
    @7
    wcel
    @21
    @7
    wcel
    @0
    @1
    @16
    @23
    @2
    @9
    cF
    cJ
    mbfimaopn.1
    mbfimaopn
    3ad2antl1
    @17
    @20
    cF
    cdm
    #
    @7
    @17
    @1
    @20
    @24
    wceq
    @22
    @1
    @20
    cA
    @24
    cA
    cB
    cF
    fimacnv
    cA
    cB
    cF
    fdm
    eqtr4d
    syl
    @17
    @0
    @24
    @7
    wcel
    @0
    @1
    @2
    @16
    simpl1
    cF
    mbfdm
    syl
    eqeltrd
    @19
    @20
    inmbl
    syl2anc
    eqeltrd
    @11
    @6
    @18
    @7
    cC
    @10
    @5
    imaeq2
    eleq1d
    syl5ibrcom
    rexlimdva
    sylbid
    imp
end
