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
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "fznn0sub.mm"
include "3ad2ant3.mm"
include "0elfz.mm"
include "syl.mm"
include "anim1i.mm"
include "swrdswrd.mm"
include "imp.mm"
include "syldan.mm"
include "elfznn0.mm"
include "nn0cn.mm"
include "addid1d.mm"
include "adantr.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ex.mm"

theorem swrd0swrd
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) /\ M e. ( 0 ... N ) ) -> ( L e. ( 0 ... ( N - M ) ) -> ( ( W substr <. M , N >. ) substr <. 0 , L >. ) = ( W substr <. M , ( M + L ) >. ) ) )

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
    #
    wcel
    #
    cW
    cM
    cN
    cop
    csubstr
    co
    cc0
    cL
    cop
    csubstr
    co
    #
    cW
    cM
    cM
    cL
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    wceq
    @3
    @6
    wa
    #
    @7
    cW
    cM
    cc0
    caddc
    co
    #
    @8
    cop
    #
    csubstr
    co
    #
    @10
    @3
    @6
    cc0
    @5
    wcel
    #
    @6
    wa
    #
    @7
    @14
    wceq
    #
    @3
    @15
    @6
    @3
    @4
    cn0
    wcel
    #
    @15
    @2
    @0
    @18
    @1
    cM
    cc0
    cN
    fznn0sub
    3ad2ant3
    @4
    0elfz
    syl
    anim1i
    @3
    @16
    @17
    cc0
    cL
    cM
    cN
    cV
    cW
    swrdswrd
    imp
    syldan
    @11
    @13
    @9
    cW
    csubstr
    @11
    @12
    cM
    @8
    @3
    @12
    cM
    wceq
    #
    @6
    @2
    @0
    @19
    @1
    @2
    cM
    cn0
    wcel
    #
    @19
    cM
    cN
    elfznn0
    @20
    cM
    cM
    nn0cn
    addid1d
    syl
    3ad2ant3
    adantr
    opeq1d
    oveq2d
    eqtrd
    ex
end
