include "cbn.mm"
include "wcel.mm"
include "wa.mm"
include "ccms.mm"
include "ccld.mm"
include "cfv.mm"
include "cnvc.mm"
include "csca.mm"
include "wb.mm"
include "bnnvc.mm"
include "lssnvc.mm"
include "sylan.mm"
include "wceq.mm"
include "eqid.mm"
include "resssca.mm"
include "adantl.mm"
include "bnsca.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "w3a.mm"
include "isbn.mm"
include "3anan32.mm"
include "bitri.mm"
include "baib.mm"
include "syl2anc.mm"
include "cbs.mm"
include "wss.mm"
include "bncms.mm"
include "lssss.mm"
include "cmsss.mm"
include "syl2an.mm"
include "bitrd.mm"

theorem lssbn
  let cS: class S
  let cU: class U
  let cJ: class J
  let cW: class W
  let cX: class X
  assume lssbn.x: |- X = ( W |`s U )
  assume lssbn.s: |- S = ( LSubSp ` W )
  assume lssbn.j: |- J = ( TopOpen ` W )


  assert |- ( ( W e. Ban /\ U e. S ) -> ( X e. Ban <-> U e. ( Clsd ` J ) ) )

  proof
    cW
    cbn
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cbn
    wcel
    #
    cX
    ccms
    wcel
    #
    cU
    cJ
    ccld
    cfv
    wcel
    #
    @2
    cX
    cnvc
    wcel
    #
    cX
    csca
    cfv
    #
    ccms
    wcel
    #
    @3
    @4
    wb
    @0
    cW
    cnvc
    wcel
    @1
    @6
    cW
    bnnvc
    cS
    cU
    cW
    cX
    lssbn.x
    lssbn.s
    lssnvc
    sylan
    @2
    cW
    csca
    cfv
    #
    @7
    ccms
    @1
    @9
    @7
    wceq
    @0
    cU
    @9
    cW
    cX
    cS
    lssbn.x
    @9
    eqid
    #
    resssca
    adantl
    @0
    @9
    ccms
    wcel
    @1
    @9
    cW
    @10
    bnsca
    adantr
    eqeltrrd
    @3
    @6
    @8
    wa
    #
    @4
    @3
    @6
    @4
    @8
    w3a
    @11
    @4
    wa
    @7
    cX
    @7
    eqid
    isbn
    @6
    @4
    @8
    3anan32
    bitri
    baib
    syl2anc
    @0
    cW
    ccms
    wcel
    cU
    cW
    cbs
    cfv
    #
    wss
    @4
    @5
    wb
    @1
    cW
    bncms
    cS
    cU
    @12
    cW
    @12
    eqid
    #
    lssbn.s
    lssss
    cU
    cJ
    cX
    cW
    @12
    lssbn.x
    @13
    lssbn.j
    cmsss
    syl2an
    bitrd
end
