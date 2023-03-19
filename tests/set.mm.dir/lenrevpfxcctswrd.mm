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
include "cpfx.mm"
include "cconcat.mm"
include "caddc.mm"
include "wceq.mm"
include "swrdcl.mm"
include "pfxcl.mm"
include "jca.mm"
include "adantr.mm"
include "ccatlen.mm"
include "syl.mm"
include "addlenrevpfx.mm"
include "eqtrd.mm"

theorem lenrevpfxcctswrd
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( # ` ( ( W substr <. M , ( # ` W ) >. ) ++ ( W prefix M ) ) ) = ( # ` W ) )

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
    #
    cW
    cM
    @2
    cop
    csubstr
    co
    #
    cW
    cM
    cpfx
    co
    #
    cconcat
    co
    chash
    cfv
    #
    @5
    chash
    cfv
    @6
    chash
    cfv
    caddc
    co
    #
    @2
    @4
    @5
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    @7
    @8
    wceq
    @1
    @11
    @3
    @1
    @9
    @10
    cV
    cW
    cM
    @2
    swrdcl
    cV
    cW
    cM
    pfxcl
    jca
    adantr
    cV
    @5
    @6
    ccatlen
    syl
    cM
    cV
    cW
    addlenrevpfx
    eqtrd
end
