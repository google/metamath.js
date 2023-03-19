include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cneg.mm"
include "cdiv.mm"
include "cif.mm"
include "cz.mm"
include "0z.mm"
include "expval.mm"
include "mpan2.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem exp0
  let cA: class A


  assert |- ( A e. CC -> ( A ^ 0 ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    cexp
    co
    #
    cc0
    cc0
    wceq
    #
    c1
    cc0
    cc0
    clt
    wbr
    cc0
    cmul
    cn
    cA
    csn
    cxp
    c1
    cseq
    #
    cfv
    c1
    cc0
    cneg
    @3
    cfv
    cdiv
    co
    cif
    #
    cif
    #
    c1
    @0
    cc0
    cz
    wcel
    @1
    @5
    wceq
    0z
    cA
    cc0
    expval
    mpan2
    @2
    c1
    @4
    cc0
    eqid
    iftruei
    syl6eq
end
