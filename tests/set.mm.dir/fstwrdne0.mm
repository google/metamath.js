include "cn.mm"
include "wcel.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "simprl.mm"
include "nnge1.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "wrdsymb1.mm"
include "syl2anc.mm"

theorem fstwrdne0
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( N e. NN /\ ( W e. Word V /\ ( # ` W ) = N ) ) -> ( W ` 0 ) e. V )

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
    #
    @1
    c1
    @2
    cle
    wbr
    #
    cc0
    cW
    cfv
    cV
    wcel
    @0
    @1
    @3
    simprl
    @5
    @6
    c1
    cN
    cle
    wbr
    #
    @0
    @7
    @4
    cN
    nnge1
    adantr
    @3
    @6
    @7
    wb
    @0
    @1
    @2
    cN
    c1
    cle
    breq2
    ad2antll
    mpbird
    cV
    cW
    wrdsymb1
    syl2anc
end
