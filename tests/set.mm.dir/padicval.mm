include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpc.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cif.mm"
include "cmpt.mm"
include "padicfval.mm"
include "fveq1d.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem padicval
  let vx: setvar x
  let cP: class P
  let cJ: class J
  let cX: class X
  let vq: setvar q
  assume padicval.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )

  disjoint q x
  disjoint P q
  disjoint P x
  disjoint X x
  assert |- ( ( P e. Prime /\ X e. QQ ) -> ( ( J ` P ) ` X ) = if ( X = 0 , 0 , ( P ^ -u ( P pCnt X ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cX
    cq
    wcel
    cX
    cP
    cJ
    cfv
    #
    cfv
    cX
    vx
    cq
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    cP
    cP
    @2
    cpc
    co
    #
    cneg
    #
    cexp
    co
    #
    cif
    #
    cmpt
    #
    cfv
    cX
    cc0
    wceq
    #
    cc0
    cP
    cP
    cX
    cpc
    co
    #
    cneg
    #
    cexp
    co
    #
    cif
    #
    @0
    cX
    @1
    @8
    vx
    cP
    cJ
    vq
    padicval.j
    padicfval
    fveq1d
    vx
    cX
    @7
    @13
    cq
    @8
    @2
    cX
    wceq
    #
    @3
    @9
    @6
    @12
    cc0
    @2
    cX
    cc0
    eqeq1
    @14
    @5
    @11
    cP
    cexp
    @14
    @4
    @10
    @2
    cX
    cP
    cpc
    oveq2
    negeqd
    oveq2d
    ifbieq2d
    @8
    eqid
    @9
    cc0
    @12
    c0ex
    cP
    @11
    cexp
    ovex
    ifex
    fvmpt
    sylan9eq
end
