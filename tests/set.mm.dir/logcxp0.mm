include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "crn.mm"
include "w3a.mm"
include "ccxp.mm"
include "ce.mm"
include "eldifi.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "eldifsni.mm"
include "simp2.mm"
include "cxpefd.mm"
include "fveq2d.mm"
include "wceq.mm"
include "logef.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem logcxp0
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( CC \ { 0 } ) /\ B e. CC /\ ( B x. ( log ` A ) ) e. ran log ) -> ( log ` ( A ^c B ) ) = ( B x. ( log ` A ) ) )

  proof
    cA
    cc
    cc0
    csn
    #
    cdif
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cA
    clog
    cfv
    cmul
    co
    #
    clog
    crn
    wcel
    #
    w3a
    #
    cA
    cB
    ccxp
    co
    #
    clog
    cfv
    @3
    ce
    cfv
    #
    clog
    cfv
    #
    @3
    @5
    @6
    @7
    clog
    @5
    cA
    cB
    @1
    @2
    cA
    cc
    wcel
    @4
    cA
    cc
    @0
    eldifi
    3ad2ant1
    @1
    @2
    cA
    cc0
    wne
    @4
    cA
    cc
    cc0
    eldifsni
    3ad2ant1
    @1
    @2
    @4
    simp2
    cxpefd
    fveq2d
    @4
    @1
    @8
    @3
    wceq
    @2
    @3
    logef
    3ad2ant3
    eqtrd
end
