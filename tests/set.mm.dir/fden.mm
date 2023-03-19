include "cq.mm"
include "cn.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdiv.mm"
include "wa.mm"
include "cz.mm"
include "cxp.mm"
include "crio.mm"
include "cdenom.mm"
include "df-denom.mm"
include "wcel.mm"
include "qdenval.mm"
include "qdencl.mm"
include "eqeltrrd.mm"
include "fmpti.mm"

theorem fden
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- denom : QQ --> NN

  proof
    va
    cq
    cn
    vb
    cv
    #
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cgcd
    co
    c1
    wceq
    va
    cv
    #
    @1
    @2
    cdiv
    co
    wceq
    wa
    vb
    cz
    cn
    cxp
    crio
    c2nd
    cfv
    #
    cdenom
    vb
    va
    df-denom
    @3
    cq
    wcel
    @3
    cdenom
    cfv
    @4
    cn
    vb
    @3
    qdenval
    @3
    qdencl
    eqeltrrd
    fmpti
end
