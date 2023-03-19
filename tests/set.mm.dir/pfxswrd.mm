include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "cpfx.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "swrdcl.mm"
include "3ad2ant1.mm"
include "elfznn0.mm"
include "pfxval.mm"
include "syl2an.mm"
include "swrd0swrd.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"

theorem pfxswrd
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) /\ M e. ( 0 ... N ) ) -> ( L e. ( 0 ... ( N - M ) ) -> ( ( W substr <. M , N >. ) prefix L ) = ( W substr <. M , ( M + L ) >. ) ) )

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
    cfz
    co
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    w3a
    #
    cL
    cc0
    cN
    cM
    cmin
    co
    #
    cfz
    co
    wcel
    #
    cW
    cM
    cN
    cop
    csubstr
    co
    #
    cL
    cpfx
    co
    #
    cW
    cM
    cM
    cL
    caddc
    co
    cop
    csubstr
    co
    #
    wceq
    @4
    @6
    wa
    @8
    @7
    cc0
    cL
    cop
    csubstr
    co
    #
    @9
    @4
    @7
    @0
    wcel
    #
    cL
    cn0
    wcel
    @8
    @10
    wceq
    @6
    @1
    @2
    @11
    @3
    cV
    cW
    cM
    cN
    swrdcl
    3ad2ant1
    cL
    @5
    elfznn0
    @7
    cL
    @0
    pfxval
    syl2an
    @4
    @6
    @10
    @9
    wceq
    cL
    cM
    cN
    cV
    cW
    swrd0swrd
    imp
    eqtrd
    ex
end
