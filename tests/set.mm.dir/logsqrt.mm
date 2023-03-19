include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "ccxp.mm"
include "csqrt.mm"
include "cc.mm"
include "wceq.mm"
include "relogcl.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "syl.mm"
include "cr.mm"
include "halfre.mm"
include "logcxp.mm"
include "mpan2.mm"
include "rpcn.mm"
include "cxpsqrt.mm"
include "fveq2d.mm"
include "3eqtr2rd.mm"

theorem logsqrt
  let cA: class A


  assert |- ( A e. RR+ -> ( log ` ( sqrt ` A ) ) = ( ( log ` A ) / 2 ) )

  proof
    cA
    crp
    wcel
    #
    cA
    clog
    cfv
    #
    c2
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    @1
    cmul
    co
    #
    cA
    @3
    ccxp
    co
    #
    clog
    cfv
    #
    cA
    csqrt
    cfv
    #
    clog
    cfv
    @0
    @1
    cc
    wcel
    #
    @2
    @4
    wceq
    #
    @0
    @1
    cA
    relogcl
    recnd
    @8
    c2
    cc
    wcel
    c2
    cc0
    wne
    @9
    2cn
    2ne0
    @1
    c2
    divrec2
    mp3an23
    syl
    @0
    @3
    cr
    wcel
    @6
    @4
    wceq
    halfre
    cA
    @3
    logcxp
    mpan2
    @0
    @5
    @7
    clog
    @0
    cA
    cc
    wcel
    @5
    @7
    wceq
    cA
    rpcn
    cA
    cxpsqrt
    syl
    fveq2d
    3eqtr2rd
end
