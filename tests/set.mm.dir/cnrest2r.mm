include "ctop.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wa.mm"
include "cuni.mm"
include "cin.mm"
include "simpr.mm"
include "cvv.mm"
include "wceq.mm"
include "cntop2.mm"
include "adantl.mm"
include "restrcl.mm"
include "eqid.mm"
include "restin.mm"
include "3syl.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "ctopon.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "simpl.mm"
include "toptopon.mm"
include "sylib.mm"
include "wf.mm"
include "cntop1.mm"
include "inss2.mm"
include "resttopon.mm"
include "sylancl.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "frn.mm"
include "syl.mm"
include "a1i.mm"
include "cnrest2.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem cnrest2r
  let cB: class B
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cY: class Y


  assert |- ( K e. Top -> ( J Cn ( K |`t B ) ) C_ ( J Cn K ) )

  proof
    cK
    ctop
    wcel
    #
    vf
    cJ
    cK
    cB
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    #
    @0
    vf
    cv
    #
    @2
    wcel
    #
    @4
    @3
    wcel
    #
    @0
    @5
    wa
    #
    @6
    @4
    cJ
    cK
    cB
    cK
    cuni
    #
    cin
    #
    crest
    co
    #
    ccn
    co
    #
    wcel
    #
    @7
    @4
    @2
    @11
    @0
    @5
    simpr
    @7
    @1
    @10
    cJ
    ccn
    @7
    @1
    ctop
    wcel
    #
    cK
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    @1
    @10
    wceq
    @5
    @13
    @0
    @4
    cJ
    @1
    cntop2
    adantl
    cB
    cK
    restrcl
    cB
    cK
    cvv
    cvv
    @8
    @8
    eqid
    #
    restin
    3syl
    oveq2d
    eleqtrd
    #
    @7
    cK
    @8
    ctopon
    cfv
    wcel
    #
    @4
    crn
    @9
    wss
    #
    @9
    @8
    wss
    #
    @6
    @12
    wb
    @7
    @0
    @16
    @0
    @5
    simpl
    cK
    @8
    @14
    toptopon
    sylib
    #
    @7
    cJ
    cuni
    #
    @9
    @4
    wf
    #
    @17
    @7
    cJ
    @20
    ctopon
    cfv
    wcel
    #
    @10
    @9
    ctopon
    cfv
    wcel
    #
    @12
    @21
    @7
    cJ
    ctop
    wcel
    #
    @22
    @5
    @24
    @0
    @4
    cJ
    @1
    cntop1
    adantl
    cJ
    @20
    @20
    eqid
    toptopon
    sylib
    @7
    @16
    @18
    @23
    @19
    cB
    @8
    inss2
    #
    @9
    cK
    @8
    resttopon
    sylancl
    @15
    @4
    cJ
    @10
    @20
    @9
    cnf2
    syl3anc
    @20
    @9
    @4
    frn
    syl
    @18
    @7
    @25
    a1i
    @9
    @4
    cJ
    cK
    @8
    cnrest2
    syl3anc
    mpbird
    ex
    ssrdv
end
