include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "3simpa.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "jca.mm"
include "swrdswrd0.mm"
include "sylc.mm"

theorem swrd0swrd0
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) /\ L e. ( 0 ... N ) ) -> ( ( W substr <. 0 , N >. ) substr <. 0 , L >. ) = ( W substr <. 0 , L >. ) )

  proof
    cW
    cV
    cword
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
    cL
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    w3a
    #
    @0
    @2
    wa
    cc0
    @3
    wcel
    #
    @4
    wa
    cW
    cc0
    cN
    cop
    csubstr
    co
    cc0
    cL
    cop
    #
    csubstr
    co
    cW
    @7
    csubstr
    co
    wceq
    @0
    @2
    @4
    3simpa
    @5
    @6
    @4
    @2
    @0
    @6
    @4
    @2
    cN
    cn0
    wcel
    @6
    cN
    @1
    elfznn0
    cN
    0elfz
    syl
    3ad2ant2
    @0
    @2
    @4
    simp3
    jca
    cc0
    cL
    cN
    cV
    cW
    swrdswrd0
    sylc
end
