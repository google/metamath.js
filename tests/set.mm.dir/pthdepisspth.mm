include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wne.mm"
include "wa.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "cspths.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wi.mm"
include "ispth.mm"
include "simplll.mm"
include "cn0.mm"
include "wcel.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "wlkcl.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "wlkp.mm"
include "simpllr.mm"
include "simpr.mm"
include "3jca.mm"
include "simplr.mm"
include "injresinj.mm"
include "syl3c.mm"
include "jca.mm"
include "ex3.mm"
include "sylbi.mm"
include "imp.mm"
include "isspth.mm"
include "sylibr.mm"

theorem pthdepisspth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( Paths ` G ) P /\ ( P ` 0 ) =/= ( P ` ( # ` F ) ) ) -> F ( SPaths ` G ) P )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cc0
    cP
    cfv
    cF
    chash
    cfv
    #
    cP
    cfv
    wne
    #
    wa
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    wa
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    @0
    @2
    @5
    @0
    @3
    cP
    c1
    @1
    cfzo
    co
    #
    cres
    ccnv
    wfun
    #
    cP
    cc0
    @1
    cpr
    cima
    cP
    @6
    cima
    cin
    c0
    wceq
    #
    w3a
    @2
    @5
    wi
    cP
    cF
    cG
    ispth
    @3
    @7
    @8
    @2
    @5
    @3
    @7
    wa
    #
    @8
    wa
    #
    @2
    wa
    #
    @3
    @4
    @3
    @7
    @8
    @2
    simplll
    @11
    @1
    cn0
    wcel
    #
    cc0
    @1
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @7
    @2
    w3a
    @8
    @4
    @3
    @12
    @7
    @8
    @2
    @3
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @12
    cP
    cF
    cG
    trliswlk
    #
    cP
    cF
    cG
    wlkcl
    syl
    ad3antrrr
    @11
    @14
    @7
    @2
    @3
    @14
    @7
    @8
    @2
    @3
    @15
    @14
    @16
    cP
    cF
    cG
    @13
    @13
    eqid
    wlkp
    syl
    ad3antrrr
    @3
    @7
    @8
    @2
    simpllr
    @10
    @2
    simpr
    3jca
    @9
    @8
    @2
    simplr
    cP
    @1
    @13
    injresinj
    syl3c
    jca
    ex3
    sylbi
    imp
    cP
    cF
    cG
    isspth
    sylibr
end
