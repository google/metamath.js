include "ccmp.mm"
include "cnlly.mm"
include "wcel.mm"
include "cuni.mm"
include "eqid.mm"
include "nllytop.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wrex.mm"
include "simpl.mm"
include "ctop.mm"
include "topopn.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "nllyi.mm"
include "syl3anc.mm"
include "reximi.mm"
include "llycmpkgen2.mm"

theorem llycmpkgen
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


  assert |- ( J e. N-Locally Comp -> J e. ran kGen )

  proof
    cJ
    ccmp
    cnlly
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
    ccmp
    cJ
    nllytop
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
    vk
    cv
    #
    @1
    wss
    #
    cJ
    @7
    crest
    co
    ccmp
    wcel
    #
    wa
    #
    vk
    @4
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wrex
    #
    @9
    vk
    @11
    wrex
    @6
    @0
    @1
    cJ
    wcel
    #
    @5
    @12
    @0
    @5
    simpl
    @0
    @13
    @5
    @0
    cJ
    ctop
    wcel
    @13
    @3
    cJ
    @1
    @2
    topopn
    syl
    adantr
    @0
    @5
    simpr
    vk
    ccmp
    @4
    @1
    cJ
    nllyi
    syl3anc
    @10
    @9
    vk
    @11
    @8
    @9
    simpr
    reximi
    syl
    llycmpkgen2
end
