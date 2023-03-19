include "cq.mm"
include "wcel.mm"
include "cdenom.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cnumer.mm"
include "cdiv.mm"
include "qeqnumdivden.mm"
include "oveq1d.mm"
include "qnumcl.mm"
include "zcnd.mm"
include "qdencl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "eqtrd.mm"

theorem qmuldeneqnum
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( A x. ( denom ` A ) ) = ( numer ` A ) )

  proof
    cA
    cq
    wcel
    #
    cA
    cA
    cdenom
    cfv
    #
    cmul
    co
    cA
    cnumer
    cfv
    #
    @1
    cdiv
    co
    #
    @1
    cmul
    co
    @2
    @0
    cA
    @3
    @1
    cmul
    cA
    qeqnumdivden
    oveq1d
    @0
    @2
    @1
    @0
    @2
    cA
    qnumcl
    zcnd
    @0
    @1
    cA
    qdencl
    #
    nncnd
    @0
    @1
    @4
    nnne0d
    divcan1d
    eqtrd
end
