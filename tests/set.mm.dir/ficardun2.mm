include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "ccrd.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "ccda.mm"
include "cen.mm"
include "uncdadom.mm"
include "cdm.mm"
include "finnum.mm"
include "cardacda.mm"
include "syl2an.mm"
include "domentr.mm"
include "syl2anc.mm"
include "wb.mm"
include "unfi.mm"
include "syl.mm"
include "com.mm"
include "con0.mm"
include "ficardom.mm"
include "nnacl.mm"
include "nnon.mm"
include "onenon.mm"
include "3syl.mm"
include "carddom2.mm"
include "mpbird.mm"
include "wceq.mm"
include "cardnn.mm"
include "sseqtrd.mm"

theorem ficardun2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( card ` ( A u. B ) ) C_ ( ( card ` A ) +o ( card ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    ccrd
    cfv
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    coa
    co
    #
    ccrd
    cfv
    #
    @7
    @2
    @4
    @8
    wss
    #
    @3
    @7
    cdom
    wbr
    #
    @2
    @3
    cA
    cB
    ccda
    co
    #
    cdom
    wbr
    @11
    @7
    cen
    wbr
    #
    @10
    cA
    cB
    cfn
    cfn
    uncdadom
    @0
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @13
    wcel
    @12
    @1
    cA
    finnum
    cB
    finnum
    cA
    cB
    cardacda
    syl2an
    @3
    @11
    @7
    domentr
    syl2anc
    @2
    @3
    @13
    wcel
    #
    @7
    @13
    wcel
    #
    @9
    @10
    wb
    @2
    @3
    cfn
    wcel
    @14
    cA
    cB
    unfi
    @3
    finnum
    syl
    @2
    @7
    com
    wcel
    #
    @7
    con0
    wcel
    @15
    @0
    @5
    com
    wcel
    @6
    com
    wcel
    @16
    @1
    cA
    ficardom
    cB
    ficardom
    @5
    @6
    nnacl
    syl2an
    #
    @7
    nnon
    @7
    onenon
    3syl
    @3
    @7
    carddom2
    syl2anc
    mpbird
    @2
    @16
    @8
    @7
    wceq
    @17
    @7
    cardnn
    syl
    sseqtrd
end
