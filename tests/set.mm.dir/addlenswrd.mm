include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "wceq.mm"
include "cc.mm"
include "swrdcl.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "syl.mm"
include "addcomd.mm"
include "adantr.mm"
include "addlenrevswrd.mm"
include "eqtrd.mm"

theorem addlenswrd
  let cM: class M
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( ( # ` ( W substr <. 0 , M >. ) ) + ( # ` ( W substr <. M , ( # ` W ) >. ) ) ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    cW
    cc0
    cM
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    cW
    cM
    @2
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    caddc
    co
    #
    @7
    @5
    caddc
    co
    #
    @2
    @1
    @8
    @9
    wceq
    @3
    @1
    @5
    @7
    @1
    @4
    @0
    wcel
    #
    @5
    cc
    wcel
    cV
    cW
    cc0
    cM
    swrdcl
    @10
    @5
    cV
    @4
    lencl
    nn0cnd
    syl
    @1
    @6
    @0
    wcel
    #
    @7
    cc
    wcel
    cV
    cW
    cM
    @2
    swrdcl
    @11
    @7
    cV
    @6
    lencl
    nn0cnd
    syl
    addcomd
    adantr
    cM
    cV
    cW
    addlenrevswrd
    eqtrd
end
