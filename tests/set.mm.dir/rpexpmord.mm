include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "oveq1.mm"
include "rpssre.mm"
include "cr.mm"
include "cn0.mm"
include "rpre.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "syl2anr.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "simplrl.mm"
include "rpred.mm"
include "simplrr.mm"
include "rpge0d.mm"
include "simpr.mm"
include "simpll.mm"
include "expmordi.mm"
include "syl221anc.mm"
include "ex.mm"
include "ltord1.mm"
include "3impb.mm"

theorem rpexpmord
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( N e. NN /\ A e. RR+ /\ B e. RR+ ) -> ( A < B <-> ( A ^ N ) < ( B ^ N ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    crp
    wcel
    cB
    crp
    wcel
    cA
    cB
    clt
    wbr
    cA
    cN
    cexp
    co
    #
    cB
    cN
    cexp
    co
    #
    clt
    wbr
    wb
    @0
    va
    vb
    va
    cv
    #
    cN
    cexp
    co
    #
    vb
    cv
    #
    cN
    cexp
    co
    #
    cA
    cB
    crp
    @1
    @2
    @3
    @5
    cN
    cexp
    oveq1
    @3
    cA
    cN
    cexp
    oveq1
    @3
    cB
    cN
    cexp
    oveq1
    rpssre
    @3
    crp
    wcel
    #
    @3
    cr
    wcel
    #
    cN
    cn0
    wcel
    @4
    cr
    wcel
    @0
    @3
    rpre
    cN
    nnnn0
    @3
    cN
    reexpcl
    syl2anr
    @0
    @7
    @5
    crp
    wcel
    #
    wa
    #
    wa
    #
    @3
    @5
    clt
    wbr
    #
    @4
    @6
    clt
    wbr
    #
    @11
    @12
    wa
    #
    @8
    @5
    cr
    wcel
    cc0
    @3
    cle
    wbr
    @12
    @0
    @13
    @14
    @3
    @0
    @7
    @9
    @12
    simplrl
    #
    rpred
    @14
    @5
    @0
    @7
    @9
    @12
    simplrr
    rpred
    @14
    @3
    @15
    rpge0d
    @11
    @12
    simpr
    @0
    @10
    @12
    simpll
    @3
    @5
    cN
    expmordi
    syl221anc
    ex
    ltord1
    3impb
end
