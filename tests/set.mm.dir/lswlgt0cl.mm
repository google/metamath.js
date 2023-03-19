include "cn.mm"
include "wcel.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "clsw.mm"
include "simprl.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "adantl.mm"
include "wi.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "syl.mm"
include "biimpd.mm"
include "adantr.mm"
include "sylbid.mm"
include "impcom.mm"
include "lswcl.mm"
include "syl2anc.mm"

theorem lswlgt0cl
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( N e. NN /\ ( W e. Word V /\ ( # ` W ) = N ) ) -> ( lastS ` W ) e. V )

  proof
    cN
    cn
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    wa
    @1
    cW
    c0
    wne
    #
    cW
    clsw
    cfv
    cV
    wcel
    @0
    @1
    @3
    simprl
    @4
    @0
    @5
    @4
    @0
    @2
    cn
    wcel
    #
    @5
    @3
    @0
    @6
    wb
    #
    @1
    @7
    cN
    @2
    cN
    @2
    cn
    eleq1
    eqcoms
    adantl
    @1
    @6
    @5
    wi
    @3
    @1
    @6
    @5
    @1
    cW
    cfn
    wcel
    @6
    @5
    wb
    cV
    cW
    wrdfin
    cW
    hashnncl
    syl
    biimpd
    adantr
    sylbid
    impcom
    cV
    cW
    lswcl
    syl2anc
end
