include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "cc.mm"
include "fveecn.mm"
include "sqsubswap.mm"
include "syl2an.mm"
include "anandirs.mm"
include "sumeq2dv.mm"
include "wb.mm"
include "id.mm"
include "simpr.mm"
include "simpl.mm"
include "brcgr.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "3adant1.mm"

theorem axcgrrflx
  let cA: class A
  let cB: class B
  let cN: class N
  let vi: setvar i


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> <. A , B >. Cgr <. B , A >. )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    cop
    cB
    cA
    cop
    ccgr
    wbr
    #
    cN
    cn
    wcel
    @1
    @2
    wa
    #
    @3
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    #
    @6
    cB
    cfv
    #
    cmin
    co
    c2
    cexp
    co
    #
    vi
    csu
    @5
    @8
    @7
    cmin
    co
    c2
    cexp
    co
    #
    vi
    csu
    wceq
    #
    @4
    @5
    @9
    @10
    vi
    @1
    @2
    @6
    @5
    wcel
    #
    @9
    @10
    wceq
    #
    @1
    @12
    wa
    @7
    cc
    wcel
    @8
    cc
    wcel
    @13
    @2
    @12
    wa
    cA
    @6
    cN
    fveecn
    cB
    @6
    cN
    fveecn
    @7
    @8
    sqsubswap
    syl2an
    anandirs
    sumeq2dv
    @4
    @4
    @2
    @1
    @3
    @11
    wb
    @4
    id
    @1
    @2
    simpr
    @1
    @2
    simpl
    cA
    cB
    cB
    cA
    vi
    cN
    brcgr
    syl12anc
    mpbird
    3adant1
end
