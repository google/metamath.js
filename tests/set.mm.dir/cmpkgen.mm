include "ccmp.mm"
include "wcel.mm"
include "cuni.mm"
include "eqid.mm"
include "cmptop.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "wrex.mm"
include "ctop.mm"
include "wss.mm"
include "adantr.mm"
include "topopn.mm"
include "syl.mm"
include "simpr.mm"
include "snssd.mm"
include "opnneiss.mm"
include "syl3anc.mm"
include "wceq.mm"
include "restid.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "llycmpkgen2.mm"

theorem cmpkgen
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( J e. Comp -> J e. ran kGen )

  proof
    cJ
    ccmp
    wcel
    #
    vx
    vk
    cJ
    cJ
    cuni
    #
    @1
    eqid
    #
    cJ
    cmptop
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    @1
    @4
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    cJ
    @1
    crest
    co
    #
    ccmp
    wcel
    #
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vk
    @8
    wrex
    @6
    cJ
    ctop
    wcel
    #
    @1
    cJ
    wcel
    #
    @7
    @1
    wss
    @9
    @0
    @15
    @5
    @3
    adantr
    #
    @6
    @15
    @16
    @17
    cJ
    @1
    @2
    topopn
    syl
    @6
    @4
    @1
    @0
    @5
    simpr
    snssd
    @7
    cJ
    @1
    opnneiss
    syl3anc
    @6
    @10
    cJ
    ccmp
    @6
    @15
    @10
    cJ
    wceq
    @17
    cJ
    ctop
    @1
    @2
    restid
    syl
    @0
    @5
    simpl
    eqeltrd
    @14
    @11
    vk
    @1
    @8
    @12
    @1
    wceq
    @13
    @10
    ccmp
    @12
    @1
    cJ
    crest
    oveq2
    eleq1d
    rspcev
    syl2anc
    llycmpkgen2
end
