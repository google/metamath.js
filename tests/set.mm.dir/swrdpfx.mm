include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "anim2i.mm"
include "adantr.mm"
include "pfxval.mm"
include "syl.mm"
include "oveq1d.mm"
include "swrdswrd0.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"

theorem swrdpfx
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) ) -> ( ( K e. ( 0 ... N ) /\ L e. ( K ... N ) ) -> ( ( W prefix N ) substr <. K , L >. ) = ( W substr <. K , L >. ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cN
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
    cK
    cc0
    cN
    cfz
    co
    wcel
    cL
    cK
    cN
    cfz
    co
    wcel
    wa
    #
    cW
    cN
    cpfx
    co
    #
    cK
    cL
    cop
    #
    csubstr
    co
    #
    cW
    @7
    csubstr
    co
    #
    wceq
    @4
    @5
    wa
    #
    @8
    cW
    cc0
    cN
    cop
    csubstr
    co
    #
    @7
    csubstr
    co
    #
    @9
    @10
    @6
    @11
    @7
    csubstr
    @10
    @1
    cN
    cn0
    wcel
    #
    wa
    #
    @6
    @11
    wceq
    @4
    @14
    @5
    @3
    @13
    @1
    cN
    @2
    elfznn0
    anim2i
    adantr
    cW
    cN
    @0
    pfxval
    syl
    oveq1d
    @4
    @5
    @12
    @9
    wceq
    cK
    cL
    cN
    cV
    cW
    swrdswrd0
    imp
    eqtrd
    ex
end
