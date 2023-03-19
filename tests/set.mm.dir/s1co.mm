include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cs1.mm"
include "ccom.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "s1val.mm"
include "cc.mm"
include "0cn.mm"
include "xpsng.mm"
include "mpan.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "coeq2d.mm"
include "wfn.mm"
include "ffn.mm"
include "id.mm"
include "fcoconst.mm"
include "syl2anr.mm"
include "cvv.mm"
include "fvex.mm"
include "ax-mp.mm"
include "c0ex.mm"
include "xpsn.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"

theorem s1co
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F


  assert |- ( ( S e. A /\ F : A --> B ) -> ( F o. <" S "> ) = <" ( F ` S ) "> )

  proof
    cS
    cA
    wcel
    #
    cA
    cB
    cF
    wf
    #
    wa
    #
    cF
    cS
    cs1
    #
    ccom
    cF
    cc0
    csn
    #
    cS
    csn
    cxp
    #
    ccom
    #
    cS
    cF
    cfv
    #
    cs1
    #
    @2
    @3
    @5
    cF
    @0
    @3
    @5
    wceq
    @1
    @0
    @3
    cc0
    cS
    cop
    csn
    #
    @5
    cS
    cA
    s1val
    cc0
    cc
    wcel
    @0
    @5
    @9
    wceq
    0cn
    cc0
    cS
    cc
    cA
    xpsng
    mpan
    eqtr4d
    adantr
    coeq2d
    @2
    @6
    @4
    @7
    csn
    cxp
    #
    @8
    @1
    cF
    cA
    wfn
    @0
    @6
    @10
    wceq
    @0
    cA
    cB
    cF
    ffn
    @0
    id
    cF
    @4
    cA
    cS
    fcoconst
    syl2anr
    @8
    cc0
    @7
    cop
    csn
    #
    @10
    @7
    cvv
    wcel
    @8
    @11
    wceq
    cS
    cF
    fvex
    #
    @7
    cvv
    s1val
    ax-mp
    cc0
    @7
    c0ex
    @12
    xpsn
    eqtr4i
    syl6reqr
    eqtr4d
end
