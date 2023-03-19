include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "lsw.mm"
include "adantr.mm"
include "cc0.mm"
include "cfzo.mm"
include "cn.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "syl.mm"
include "wrdsymbcl.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem lswcl
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( lastS ` W ) e. V )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    cW
    clsw
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cV
    @1
    @4
    @7
    wceq
    @2
    cW
    @0
    lsw
    adantr
    @1
    @2
    @6
    cc0
    @5
    cfzo
    co
    wcel
    #
    @7
    cV
    wcel
    @3
    @5
    cn
    wcel
    @8
    cV
    cW
    lennncl
    @5
    fzo0end
    syl
    @6
    cV
    cW
    wrdsymbcl
    syldan
    eqeltrd
end
