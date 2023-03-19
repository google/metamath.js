include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "eqid.mm"
include "wb.mm"
include "xmeteq0.mm"
include "3anidm23.mm"
include "mpbiri.mm"

theorem xmet0
  let cA: class A
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( ( D e. ( *Met ` X ) /\ A e. X ) -> ( A D A ) = 0 )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cA
    cA
    cD
    co
    cc0
    wceq
    #
    cA
    cA
    wceq
    #
    cA
    eqid
    @0
    @1
    @2
    @3
    wb
    cA
    cA
    cD
    cX
    xmeteq0
    3anidm23
    mpbiri
end
