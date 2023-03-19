include "ctop.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "wa.mm"
include "ckgen.mm"
include "cfv.mm"
include "wss.mm"
include "kgenftop.mm"
include "adantr.mm"
include "kgenss.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "cmptop.mm"
include "adantl.mm"
include "restrcl.mm"
include "simprd.mm"
include "syl.mm"
include "restval.mm"
include "wf.mm"
include "simpr.mm"
include "simplr.mm"
include "kgeni.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "eqssd.mm"

theorem kgencmp
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( J e. Top /\ ( J |`t K ) e. Comp ) -> ( J |`t K ) = ( ( kGen ` J ) |`t K ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    cK
    crest
    co
    #
    ccmp
    wcel
    #
    wa
    #
    @1
    cJ
    ckgen
    cfv
    #
    cK
    crest
    co
    #
    @3
    @4
    ctop
    wcel
    #
    cJ
    @4
    wss
    #
    @1
    @5
    wss
    @0
    @6
    @2
    cJ
    kgenftop
    adantr
    #
    @0
    @7
    @2
    cJ
    kgenss
    adantr
    cK
    cJ
    @4
    ctop
    ssrest
    syl2anc
    @3
    @5
    vx
    @4
    vx
    cv
    #
    cK
    cin
    #
    cmpt
    #
    crn
    #
    @1
    @3
    @6
    cK
    cvv
    wcel
    #
    @5
    @12
    wceq
    @8
    @3
    @1
    ctop
    wcel
    #
    @13
    @2
    @14
    @0
    @1
    cmptop
    adantl
    @14
    cJ
    cvv
    wcel
    @13
    cK
    cJ
    restrcl
    simprd
    syl
    vx
    cK
    @4
    ctop
    cvv
    restval
    syl2anc
    @3
    @4
    @1
    @11
    wf
    @12
    @1
    wss
    @3
    vx
    @4
    @10
    @1
    @11
    @3
    @9
    @4
    wcel
    #
    wa
    @15
    @2
    @10
    @1
    wcel
    @3
    @15
    simpr
    @0
    @2
    @15
    simplr
    @9
    cJ
    cK
    kgeni
    syl2anc
    @11
    eqid
    fmptd
    @4
    @1
    @11
    frn
    syl
    eqsstrd
    eqssd
end
