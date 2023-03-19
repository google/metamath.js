include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "clp.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "wa.mm"
include "wceq.mm"
include "simp3.mm"
include "ssdifssd.mm"
include "restcls.mm"
include "syld3an3.mm"
include "eleq2d.mm"
include "elin.mm"
include "syl6bb.mm"
include "cuni.mm"
include "wb.mm"
include "ctopon.mm"
include "crest.mm"
include "co.mm"
include "simp1.mm"
include "toptopon.mm"
include "sylib.mm"
include "simp2.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "syl.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "islp.mm"
include "sstrd.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem restlp
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vx: setvar x
  assume restcls.1: |- X = U. J
  assume restcls.2: |- K = ( J |`t Y )


  assert |- ( ( J e. Top /\ Y C_ X /\ S C_ Y ) -> ( ( limPt ` K ) ` S ) = ( ( ( limPt ` J ) ` S ) i^i Y ) )

  proof
    cJ
    ctop
    wcel
    #
    cY
    cX
    wss
    #
    cS
    cY
    wss
    #
    w3a
    #
    vx
    cS
    cK
    clp
    cfv
    cfv
    #
    cS
    cJ
    clp
    cfv
    cfv
    #
    cY
    cin
    #
    @3
    vx
    cv
    #
    cS
    @7
    csn
    #
    cdif
    #
    cK
    ccl
    cfv
    cfv
    #
    wcel
    #
    @7
    @9
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @7
    cY
    wcel
    #
    wa
    #
    @7
    @4
    wcel
    #
    @7
    @6
    wcel
    #
    @3
    @11
    @7
    @12
    cY
    cin
    #
    wcel
    @15
    @3
    @10
    @18
    @7
    @0
    @1
    @2
    @9
    cY
    wss
    @10
    @18
    wceq
    @3
    cS
    cY
    @8
    @0
    @1
    @2
    simp3
    #
    ssdifssd
    @9
    cJ
    cK
    cX
    cY
    restcls.1
    restcls.2
    restcls
    syld3an3
    eleq2d
    @7
    @12
    cY
    elin
    syl6bb
    @3
    cK
    ctop
    wcel
    #
    cS
    cK
    cuni
    #
    wss
    @16
    @11
    wb
    @3
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @20
    @3
    cK
    cJ
    cY
    crest
    co
    #
    @22
    restcls.2
    @3
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @24
    @22
    wcel
    @3
    @0
    @25
    @0
    @1
    @2
    simp1
    #
    cJ
    cX
    restcls.1
    toptopon
    sylib
    @0
    @1
    @2
    simp2
    #
    cY
    cJ
    cX
    resttopon
    syl2anc
    syl5eqel
    #
    cY
    cK
    topontop
    syl
    @3
    cS
    cY
    @21
    @19
    @3
    @23
    cY
    @21
    wceq
    @28
    cY
    cK
    toponuni
    syl
    sseqtrd
    @7
    cS
    cK
    @21
    @21
    eqid
    islp
    syl2anc
    @17
    @7
    @5
    wcel
    #
    @14
    wa
    @3
    @15
    @7
    @5
    cY
    elin
    @3
    @29
    @13
    @14
    @3
    @0
    cS
    cX
    wss
    @29
    @13
    wb
    @26
    @3
    cS
    cY
    cX
    @19
    @27
    sstrd
    @7
    cS
    cJ
    cX
    restcls.1
    islp
    syl2anc
    anbi1d
    syl5bb
    3bitr4d
    eqrdv
end
