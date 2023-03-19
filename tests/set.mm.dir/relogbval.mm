include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "clogb.mm"
include "co.mm"
include "clog.mm"
include "cdiv.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "zgt1rpn0n1.mm"
include "adantr.mm"
include "simp1d.mm"
include "rpcnd.mm"
include "simp2d.mm"
include "simp3d.mm"
include "eldifpr.mm"
include "syl3anbrc.mm"
include "simpr.mm"
include "rpcnne0d.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "logbval.mm"
include "syl2anc.mm"

theorem relogbval
  let cB: class B
  let cX: class X


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ ) -> ( B logb X ) = ( ( log ` X ) / ( log ` B ) ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cX
    crp
    wcel
    #
    wa
    #
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cX
    cc
    cc0
    csn
    cdif
    wcel
    #
    cB
    cX
    clogb
    co
    cX
    clog
    cfv
    cB
    clog
    cfv
    cdiv
    co
    wceq
    @2
    cB
    cc
    wcel
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    @3
    @2
    cB
    @2
    cB
    crp
    wcel
    #
    @5
    @6
    @0
    @7
    @5
    @6
    w3a
    @1
    cB
    zgt1rpn0n1
    adantr
    #
    simp1d
    rpcnd
    @2
    @7
    @5
    @6
    @8
    simp2d
    @2
    @7
    @5
    @6
    @8
    simp3d
    cB
    cc
    cc0
    c1
    eldifpr
    syl3anbrc
    @2
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    @4
    @2
    cX
    @0
    @1
    simpr
    rpcnne0d
    cX
    cc
    cc0
    eldifsn
    sylibr
    cB
    cX
    logbval
    syl2anc
end
