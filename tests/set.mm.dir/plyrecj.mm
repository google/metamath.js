include "cr.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ccoe.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "ccj.mm"
include "fzfid.mm"
include "cn0.mm"
include "wf.mm"
include "0re.mm"
include "eqid.mm"
include "coef2.mm"
include "mpan2.mm"
include "adantr.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "recnd.mm"
include "simpr.mm"
include "expcl.mm"
include "mulcld.mm"
include "fsumcj.mm"
include "cjmuld.mm"
include "cjred.mm"
include "wceq.mm"
include "cjexp.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "coeid2.mm"
include "fveq2d.mm"
include "cjcl.mm"
include "sylan2.mm"
include "3eqtr4d.mm"

theorem plyrecj
  let cA: class A
  let cF: class F
  let vx: setvar x
  let cG: class G
  let cS: class S
  let cV: class V


  assert |- ( ( F e. ( Poly ` RR ) /\ A e. CC ) -> ( * ` ( F ` A ) ) = ( F ` ( * ` A ) ) )

  proof
    cF
    cr
    cply
    cfv
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vx
    cv
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    cA
    @5
    cexp
    co
    #
    cmul
    co
    #
    vx
    csu
    #
    ccj
    cfv
    #
    @4
    @7
    cA
    ccj
    cfv
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    vx
    csu
    #
    cA
    cF
    cfv
    #
    ccj
    cfv
    @12
    cF
    cfv
    #
    @2
    @11
    @4
    @9
    ccj
    cfv
    #
    vx
    csu
    @15
    @2
    @4
    @9
    vx
    @2
    cc0
    @3
    fzfid
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @7
    @8
    @20
    @7
    @2
    cn0
    cr
    @6
    wf
    #
    @5
    cn0
    wcel
    #
    @7
    cr
    wcel
    @19
    @0
    @21
    @1
    @0
    cc0
    cr
    wcel
    @21
    0re
    @6
    cr
    cF
    @6
    eqid
    #
    coef2
    mpan2
    adantr
    @5
    @3
    elfznn0
    #
    cn0
    cr
    @5
    @6
    ffvelrn
    syl2an
    #
    recnd
    #
    @2
    @1
    @22
    @8
    cc
    wcel
    @19
    @0
    @1
    simpr
    #
    @24
    cA
    @5
    expcl
    syl2an
    #
    mulcld
    fsumcj
    @2
    @4
    @18
    @14
    vx
    @20
    @18
    @7
    ccj
    cfv
    #
    @8
    ccj
    cfv
    #
    cmul
    co
    @14
    @20
    @7
    @8
    @26
    @28
    cjmuld
    @20
    @29
    @7
    @30
    @13
    cmul
    @20
    @7
    @25
    cjred
    @2
    @1
    @22
    @30
    @13
    wceq
    @19
    @27
    @24
    cA
    @5
    cjexp
    syl2an
    oveq12d
    eqtrd
    sumeq2dv
    eqtrd
    @2
    @16
    @10
    ccj
    @6
    cr
    vx
    cF
    @3
    cA
    @23
    @3
    eqid
    #
    coeid2
    fveq2d
    @1
    @0
    @12
    cc
    wcel
    @17
    @15
    wceq
    cA
    cjcl
    @6
    cr
    vx
    cF
    @3
    @12
    @23
    @31
    coeid2
    sylan2
    3eqtr4d
end
