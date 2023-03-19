include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cvv.mm"
include "topontop.mm"
include "adantr.mm"
include "id.mm"
include "toponmax.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "resttop.mm"
include "syl2anc.mm"
include "cin.mm"
include "simpr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "simpl.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "syl.mm"
include "cpw.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "restval.mm"
include "syldan.mm"
include "wf.mm"
include "inss2.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "mpbir.mm"
include "a1i.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "sspwuni.mm"
include "eqssd.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem resttopon
  let cA: class A
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( J e. ( TopOn ` X ) /\ A C_ X ) -> ( J |`t A ) e. ( TopOn ` A ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    ctop
    wcel
    #
    cA
    @4
    cuni
    #
    wceq
    @4
    cA
    ctopon
    cfv
    wcel
    @3
    cJ
    ctop
    wcel
    #
    cA
    cvv
    wcel
    #
    @5
    @1
    @7
    @2
    cX
    cJ
    topontop
    adantr
    @2
    @2
    cX
    cJ
    wcel
    #
    @8
    @1
    @2
    id
    cX
    cJ
    toponmax
    #
    cA
    cX
    cJ
    ssexg
    syl2anr
    #
    cA
    cJ
    cvv
    resttop
    syl2anc
    @3
    cA
    @6
    @3
    cA
    @4
    wcel
    cA
    @6
    wss
    @3
    cX
    cA
    cin
    #
    cA
    @4
    @3
    @2
    @12
    cA
    wceq
    @1
    @2
    simpr
    cA
    cX
    sseqin2
    sylib
    @3
    @1
    @8
    @9
    @12
    @4
    wcel
    @1
    @2
    simpl
    @11
    @1
    @9
    @2
    @10
    adantr
    cX
    cA
    cJ
    @0
    cvv
    elrestr
    syl3anc
    eqeltrrd
    cA
    @4
    elssuni
    syl
    @3
    @4
    cA
    cpw
    #
    wss
    @6
    cA
    wss
    @3
    @4
    vx
    cJ
    vx
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    @13
    @1
    @2
    @8
    @4
    @17
    wceq
    @11
    vx
    cA
    cJ
    @0
    cvv
    restval
    syldan
    @3
    cJ
    @13
    @16
    wf
    @17
    @13
    wss
    @3
    vx
    cJ
    @15
    @13
    @16
    @15
    @13
    wcel
    #
    @3
    @14
    cJ
    wcel
    wa
    @18
    @15
    cA
    wss
    @14
    cA
    inss2
    @15
    cA
    @14
    cA
    vx
    vex
    inex1
    elpw
    mpbir
    a1i
    @16
    eqid
    fmptd
    cJ
    @13
    @16
    frn
    syl
    eqsstrd
    @4
    cA
    sspwuni
    sylib
    eqssd
    cA
    @4
    istopon
    sylanbrc
end
