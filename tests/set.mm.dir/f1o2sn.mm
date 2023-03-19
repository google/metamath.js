include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "wf1o.mm"
include "cxp.mm"
include "cvv.mm"
include "opex.mm"
include "simpr.mm"
include "f1osng.mm"
include "sylancr.mm"
include "wceq.mm"
include "wb.mm"
include "xpsng.mm"
include "anidms.mm"
include "eqcomd.mm"
include "adantr.mm"
include "f1oeq2.mm"
include "syl.mm"
include "mpbid.mm"

theorem f1o2sn
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( E e. V /\ X e. W ) -> { <. <. E , E >. , X >. } : ( { E } X. { E } ) -1-1-onto-> { X } )

  proof
    cE
    cV
    wcel
    #
    cX
    cW
    wcel
    #
    wa
    #
    cE
    cE
    cop
    #
    csn
    #
    cX
    csn
    #
    @3
    cX
    cop
    csn
    #
    wf1o
    #
    cE
    csn
    #
    @8
    cxp
    #
    @5
    @6
    wf1o
    #
    @2
    @3
    cvv
    wcel
    @1
    @7
    cE
    cE
    opex
    @0
    @1
    simpr
    @3
    cX
    cvv
    cW
    f1osng
    sylancr
    @2
    @4
    @9
    wceq
    #
    @7
    @10
    wb
    @0
    @11
    @1
    @0
    @9
    @4
    @0
    @9
    @4
    wceq
    cE
    cE
    cV
    cV
    xpsng
    anidms
    eqcomd
    adantr
    @4
    @9
    @5
    @6
    f1oeq2
    syl
    mpbid
end
