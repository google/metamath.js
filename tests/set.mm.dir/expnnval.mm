include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cneg.mm"
include "cdiv.mm"
include "cif.mm"
include "cz.mm"
include "nnz.mm"
include "expval.mm"
include "sylan2.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "nngt0.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "adantl.mm"

theorem expnnval
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN ) -> ( A ^ N ) = ( seq 1 ( x. , ( NN X. { A } ) ) ` N ) )

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
    cA
    cN
    cexp
    co
    #
    cN
    cc0
    wceq
    #
    c1
    cc0
    cN
    clt
    wbr
    #
    cN
    cmul
    cn
    cA
    csn
    cxp
    c1
    cseq
    #
    cfv
    #
    c1
    cN
    cneg
    @5
    cfv
    cdiv
    co
    #
    cif
    #
    cif
    #
    @6
    @1
    @0
    cN
    cz
    wcel
    @2
    @9
    wceq
    cN
    nnz
    cA
    cN
    expval
    sylan2
    @1
    @9
    @6
    wceq
    @0
    @1
    @9
    @8
    @6
    @1
    @3
    c1
    @8
    @1
    cN
    cc0
    cN
    nnne0
    neneqd
    iffalsed
    @1
    @4
    @6
    @7
    cN
    nngt0
    iftrued
    eqtrd
    adantl
    eqtrd
end
