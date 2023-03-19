include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "ccxp.mm"
include "cexp.mm"
include "nncn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "recid2d.mm"
include "oveq2d.mm"
include "cn0.mm"
include "wceq.mm"
include "simpl.mm"
include "cr.mm"
include "nnrecre.mm"
include "recnd.mm"
include "nnnn0.mm"
include "cxpmul2.mm"
include "syl3anc.mm"
include "cxp1.mm"
include "adantr.mm"
include "3eqtr3d.mm"

theorem cxproot
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN ) -> ( ( A ^c ( 1 / N ) ) ^ N ) = A )

  proof
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    c1
    cN
    cdiv
    co
    #
    cN
    cmul
    co
    #
    ccxp
    co
    #
    cA
    c1
    ccxp
    co
    #
    cA
    @3
    ccxp
    co
    cN
    cexp
    co
    #
    cA
    @2
    @4
    c1
    cA
    ccxp
    @2
    cN
    @1
    cN
    cc
    wcel
    @0
    cN
    nncn
    adantl
    @1
    cN
    cc0
    wne
    @0
    cN
    nnne0
    adantl
    recid2d
    oveq2d
    @2
    @0
    @3
    cc
    wcel
    cN
    cn0
    wcel
    #
    @5
    @7
    wceq
    @0
    @1
    simpl
    @2
    @3
    @1
    @3
    cr
    wcel
    @0
    cN
    nnrecre
    adantl
    recnd
    @1
    @8
    @0
    cN
    nnnn0
    adantl
    cA
    @3
    cN
    cxpmul2
    syl3anc
    @0
    @6
    cA
    wceq
    @1
    cA
    cxp1
    adantr
    3eqtr3d
end
