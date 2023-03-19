include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "wceq.mm"
include "w3a.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "wi.mm"
include "wa.mm"
include "upgredginwlk.mm"
include "ancoms.mm"
include "imp.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "ralimdva.mm"
include "impancom.mm"
include "3adant2.mm"
include "com12.mm"
include "sylbid.mm"

theorem upgrwlkvtxedg
  let cP: class P
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let ve: setvar e
  assume wlkvtxedg.e: |- E = ( Edg ` G )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint E e
  disjoint F e
  disjoint e k
  disjoint G e
  disjoint P e
  assert |- ( ( G e. UPGraph /\ F ( Walks ` G ) P ) -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } e. E )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    vk
    cv
    #
    cP
    cfv
    @2
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    cE
    wcel
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @0
    @1
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    @5
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @2
    cF
    cfv
    @8
    cfv
    #
    @3
    wceq
    #
    vk
    @6
    wral
    #
    w3a
    #
    @7
    cP
    vk
    cF
    cG
    @8
    @10
    @10
    eqid
    @8
    eqid
    #
    upgriswlk
    @15
    @0
    @7
    @9
    @14
    @0
    @7
    wi
    @11
    @9
    @0
    @14
    @7
    @9
    @0
    wa
    #
    @13
    @4
    vk
    @6
    @17
    @2
    @6
    wcel
    #
    wa
    @4
    @13
    @12
    cE
    wcel
    #
    @17
    @18
    @19
    @0
    @9
    @18
    @19
    wi
    cE
    cF
    cG
    @8
    @2
    @16
    wlkvtxedg.e
    upgredginwlk
    ancoms
    imp
    @4
    @19
    wb
    @3
    @12
    @3
    @12
    cE
    eleq1
    eqcoms
    syl5ibrcom
    ralimdva
    impancom
    3adant2
    com12
    sylbid
    imp
end
