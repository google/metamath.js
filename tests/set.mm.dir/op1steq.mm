include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "wb.mm"
include "xpss.mm"
include "sseli.mm"
include "wa.mm"
include "c2nd.mm"
include "eqid.mm"
include "eqopi.mm"
include "mpanr2.mm"
include "fvex.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "syl.mm"
include "ex.mm"
include "eqop.mm"
include "simpl.mm"
include "syl6bi.mm"
include "exlimdv.mm"
include "impbid.mm"

theorem op1steq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  assert |- ( A e. ( V X. W ) -> ( ( 1st ` A ) = B <-> E. x A = <. B , x >. ) )

  proof
    cA
    cV
    cW
    cxp
    #
    wcel
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    cB
    wceq
    #
    cA
    cB
    vx
    cv
    #
    cop
    #
    wceq
    #
    vx
    wex
    #
    wb
    @0
    @1
    cA
    cV
    cW
    xpss
    sseli
    @2
    @3
    @7
    @2
    @3
    @7
    @2
    @3
    wa
    cA
    cB
    cA
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @7
    @2
    @3
    @8
    @8
    wceq
    @10
    @8
    eqid
    cA
    cB
    @8
    cvv
    cvv
    eqopi
    mpanr2
    @6
    @10
    vx
    @8
    cA
    c2nd
    fvex
    @4
    @8
    wceq
    @5
    @9
    cA
    @4
    @8
    cB
    opeq2
    eqeq2d
    spcev
    syl
    ex
    @2
    @6
    @3
    vx
    @2
    @6
    @3
    @8
    @4
    wceq
    #
    wa
    @3
    cA
    cB
    @4
    cvv
    cvv
    eqop
    @3
    @11
    simpl
    syl6bi
    exlimdv
    impbid
    syl
end
