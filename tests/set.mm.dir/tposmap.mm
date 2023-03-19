include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "ctpos.mm"
include "wf.mm"
include "elmapi.mm"
include "tposf.mm"
include "syl.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "elmapex.mm"
include "ccnv.mm"
include "cnvxp.mm"
include "cnvexg.mm"
include "syl5eqelr.mm"
include "anim2i.mm"
include "elmapg.mm"
include "3syl.mm"
include "mpbird.mm"

theorem tposmap
  let cA: class A
  let cB: class B
  let cI: class I
  let cJ: class J


  assert |- ( A e. ( B ^m ( I X. J ) ) -> tpos A e. ( B ^m ( J X. I ) ) )

  proof
    cA
    cB
    cI
    cJ
    cxp
    #
    cmap
    co
    wcel
    #
    cA
    ctpos
    #
    cB
    cJ
    cI
    cxp
    #
    cmap
    co
    wcel
    #
    @3
    cB
    @2
    wf
    #
    @1
    @0
    cB
    cA
    wf
    @5
    cA
    cB
    @0
    elmapi
    cI
    cJ
    cB
    cA
    tposf
    syl
    @1
    cB
    cvv
    wcel
    #
    @0
    cvv
    wcel
    #
    wa
    @6
    @3
    cvv
    wcel
    #
    wa
    @4
    @5
    wb
    cA
    cB
    @0
    elmapex
    @7
    @8
    @6
    @7
    @3
    @0
    ccnv
    cvv
    cI
    cJ
    cnvxp
    @0
    cvv
    cnvexg
    syl5eqelr
    anim2i
    cB
    @3
    @2
    cvv
    cvv
    elmapg
    3syl
    mpbird
end
