include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctg.mm"
include "cfv.mm"
include "tgrest.mm"
include "wceq.mm"
include "tgtop.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "ctb.mm"
include "topbas.mm"
include "restbas.mm"
include "tgcl.mm"
include "3syl.mm"
include "eqeltrrd.mm"

theorem resttop
  let cA: class A
  let cJ: class J
  let cV: class V
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
  let cX: class X
  let cW: class W


  assert |- ( ( J e. Top /\ A e. V ) -> ( J |`t A ) e. Top )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    ctg
    cfv
    #
    @3
    ctop
    @2
    @4
    cJ
    ctg
    cfv
    #
    cA
    crest
    co
    @3
    cA
    cJ
    ctop
    cV
    tgrest
    @2
    @5
    cJ
    cA
    crest
    @0
    @5
    cJ
    wceq
    @1
    cJ
    tgtop
    adantr
    oveq1d
    eqtrd
    @2
    cJ
    ctb
    wcel
    #
    @3
    ctb
    wcel
    @4
    ctop
    wcel
    @0
    @6
    @1
    cJ
    topbas
    adantr
    cA
    cJ
    restbas
    @3
    tgcl
    3syl
    eqeltrrd
end
