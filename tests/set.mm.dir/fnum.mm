include "cq.mm"
include "cz.mm"
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
include "cn.mm"
include "cxp.mm"
include "crio.mm"
include "cnumer.mm"
include "df-numer.mm"
include "wcel.mm"
include "qnumval.mm"
include "qnumcl.mm"
include "eqeltrrd.mm"
include "fmpti.mm"

theorem fnum
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- numer : QQ --> ZZ

  proof
    va
    cq
    cz
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
    c1st
    cfv
    #
    cnumer
    vb
    va
    df-numer
    @3
    cq
    wcel
    @3
    cnumer
    cfv
    @4
    cz
    vb
    @3
    qnumval
    @3
    qnumcl
    eqeltrrd
    fmpti
end
