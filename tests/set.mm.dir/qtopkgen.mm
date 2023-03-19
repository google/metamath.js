include "ckgen.mm"
include "crn.mm"
include "wcel.mm"
include "wfn.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "ctop.mm"
include "cfv.mm"
include "wss.mm"
include "kgentop.mm"
include "qtoptop.mm"
include "sylan.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cuni.mm"
include "elssuni.mm"
include "adantl.mm"
include "wceq.mm"
include "adantr.mm"
include "eqid.mm"
include "kgenuni.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "wfo.mm"
include "simpll.mm"
include "simplr.mm"
include "dffn4.mm"
include "sylib.mm"
include "qtopuni.mm"
include "syl2anc.mm"
include "ccn.mm"
include "ctopon.mm"
include "toptopon.mm"
include "qtopid.mm"
include "kgencn3.mm"
include "eleqtrd.mm"
include "cnima.mm"
include "sylancom.mm"
include "wb.mm"
include "elqtop2.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "iskgen2.mm"
include "sylanbrc.mm"

theorem qtopkgen
  let cF: class F
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume qtopcmp.1: |- X = U. J


  assert |- ( ( J e. ran kGen /\ F Fn X ) -> ( J qTop F ) e. ran kGen )

  proof
    cJ
    ckgen
    crn
    #
    wcel
    #
    cF
    cX
    wfn
    #
    wa
    #
    cJ
    cF
    cqtop
    co
    #
    ctop
    wcel
    #
    @4
    ckgen
    cfv
    #
    @4
    wss
    @4
    @0
    wcel
    @1
    cJ
    ctop
    wcel
    #
    @2
    @5
    cJ
    kgentop
    #
    cF
    cJ
    cX
    qtopcmp.1
    qtoptop
    sylan
    #
    @3
    vx
    @6
    @4
    @3
    vx
    cv
    #
    @6
    wcel
    #
    @10
    @4
    wcel
    #
    @3
    @11
    wa
    #
    @12
    @10
    cF
    crn
    #
    wss
    #
    cF
    ccnv
    @10
    cima
    cJ
    wcel
    #
    @13
    @10
    @4
    cuni
    #
    @14
    @13
    @10
    @6
    cuni
    #
    @17
    @11
    @10
    @18
    wss
    @3
    @10
    @6
    elssuni
    adantl
    @13
    @5
    @17
    @18
    wceq
    @3
    @5
    @11
    @9
    adantr
    #
    @4
    @17
    @17
    eqid
    kgenuni
    syl
    sseqtr4d
    @13
    @7
    cX
    @14
    cF
    wfo
    #
    @14
    @17
    wceq
    @13
    @1
    @7
    @1
    @2
    @11
    simpll
    #
    @8
    syl
    #
    @13
    @2
    @20
    @1
    @2
    @11
    simplr
    #
    cX
    cF
    dffn4
    sylib
    #
    cF
    cJ
    cX
    @14
    qtopcmp.1
    qtopuni
    syl2anc
    sseqtr4d
    @3
    @11
    cF
    cJ
    @6
    ccn
    co
    #
    wcel
    @16
    @13
    cF
    cJ
    @4
    ccn
    co
    #
    @25
    @13
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @2
    cF
    @26
    wcel
    @13
    @7
    @27
    @22
    cJ
    cX
    qtopcmp.1
    toptopon
    sylib
    @23
    cF
    cJ
    cX
    qtopid
    syl2anc
    @13
    @1
    @5
    @26
    @25
    wceq
    @21
    @19
    cJ
    @4
    kgencn3
    syl2anc
    eleqtrd
    @10
    cF
    cJ
    @6
    cnima
    sylancom
    @13
    @1
    @20
    @12
    @15
    @16
    wa
    wb
    @21
    @24
    @10
    cF
    cJ
    @0
    cX
    @14
    qtopcmp.1
    elqtop2
    syl2anc
    mpbir2and
    ex
    ssrdv
    @4
    iskgen2
    sylanbrc
end
