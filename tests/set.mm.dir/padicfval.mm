include "cq.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpc.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cif.mm"
include "cmpt.mm"
include "cprime.mm"
include "id.mm"
include "oveq1.mm"
include "negeqd.mm"
include "oveq12d.mm"
include "ifeq2d.mm"
include "mpteq2dv.mm"
include "qex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem padicfval
  let vx: setvar x
  let cP: class P
  let cJ: class J
  let vq: setvar q
  let cX: class X
  assume padicval.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )

  disjoint q x
  disjoint P q
  disjoint P x
  disjoint X x
  assert |- ( P e. Prime -> ( J ` P ) = ( x e. QQ |-> if ( x = 0 , 0 , ( P ^ -u ( P pCnt x ) ) ) ) )

  proof
    vq
    cP
    vx
    cq
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    vq
    cv
    #
    @2
    @0
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
    vx
    cq
    @1
    cc0
    cP
    cP
    @0
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
    cprime
    cJ
    @2
    cP
    wceq
    #
    vx
    cq
    @6
    @10
    @11
    @1
    @5
    @9
    cc0
    @11
    @2
    cP
    @4
    @8
    cexp
    @11
    id
    @11
    @3
    @7
    @2
    cP
    @0
    cpc
    oveq1
    negeqd
    oveq12d
    ifeq2d
    mpteq2dv
    padicval.j
    vx
    cq
    @10
    qex
    mptex
    fvmpt
end
