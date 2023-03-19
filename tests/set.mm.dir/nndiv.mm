include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cmul.mm"
include "risset.mm"
include "eqcom.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divmuld.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "syl5rbb.mm"

theorem nndiv
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. NN /\ B e. NN ) -> ( E. x e. NN ( A x. x ) = B <-> ( B / A ) e. NN ) )

  proof
    cB
    cA
    cdiv
    co
    #
    cn
    wcel
    vx
    cv
    #
    @0
    wceq
    #
    vx
    cn
    wrex
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    @1
    cmul
    co
    cB
    wceq
    #
    vx
    cn
    wrex
    vx
    @0
    cn
    risset
    @5
    @2
    @6
    vx
    cn
    @2
    @0
    @1
    wceq
    @5
    @1
    cn
    wcel
    #
    wa
    #
    @6
    @1
    @0
    eqcom
    @8
    cB
    cA
    @1
    @4
    cB
    cc
    wcel
    @3
    @7
    cB
    nncn
    ad2antlr
    @3
    cA
    cc
    wcel
    @4
    @7
    cA
    nncn
    ad2antrr
    @7
    @1
    cc
    wcel
    @5
    @1
    nncn
    adantl
    @3
    cA
    cc0
    wne
    @4
    @7
    cA
    nnne0
    ad2antrr
    divmuld
    syl5bb
    rexbidva
    syl5rbb
end
