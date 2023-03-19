include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "caddc.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "efaddlem.mm"

theorem efadd
  let cA: class A
  let cB: class B
  let vn: setvar n


  assert |- ( ( A e. CC /\ B e. CC ) -> ( exp ` ( A + B ) ) = ( ( exp ` A ) x. ( exp ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cA
    cB
    vn
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    @2
    cfa
    cfv
    #
    cdiv
    co
    cmpt
    #
    vn
    cn0
    cB
    @2
    cexp
    co
    @3
    cdiv
    co
    cmpt
    #
    vn
    cn0
    cA
    cB
    caddc
    co
    @2
    cexp
    co
    @3
    cdiv
    co
    cmpt
    #
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    efaddlem
end
