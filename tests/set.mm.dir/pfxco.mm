include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "ccom.mm"
include "cpfx.mm"
include "wa.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "3ad2ant2.mm"
include "0elfz.mm"
include "syl.mm"
include "simp2.mm"
include "jca.mm"
include "swrdco.mm"
include "syld3an2.mm"
include "pfxval.mm"
include "sylan2.mm"
include "coeq2d.mm"
include "3adant3.mm"
include "cvv.mm"
include "wfun.mm"
include "ffun.mm"
include "anim2i.mm"
include "ancomd.mm"
include "3adant2.mm"
include "cofunexg.mm"
include "3eqtr4d.mm"

theorem pfxco
  let cA: class A
  let cB: class B
  let cF: class F
  let cN: class N
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word A /\ N e. ( 0 ... ( # ` W ) ) /\ F : A --> B ) -> ( F o. ( W prefix N ) ) = ( ( F o. W ) prefix N ) )

  proof
    cW
    cA
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
    cA
    cB
    cF
    wf
    #
    w3a
    #
    cF
    cW
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    ccom
    #
    cF
    cW
    ccom
    #
    @6
    csubstr
    co
    #
    cF
    cW
    cN
    cpfx
    co
    #
    ccom
    #
    @9
    cN
    cpfx
    co
    #
    @1
    cc0
    cc0
    cN
    cfz
    co
    wcel
    #
    @3
    wa
    @3
    @4
    @8
    @10
    wceq
    @5
    @14
    @3
    @5
    cN
    cn0
    wcel
    #
    @14
    @3
    @1
    @15
    @4
    cN
    @2
    elfznn0
    #
    3ad2ant2
    #
    cN
    0elfz
    syl
    @1
    @3
    @4
    simp2
    jca
    cA
    cB
    cF
    cc0
    cN
    cW
    swrdco
    syld3an2
    @1
    @3
    @12
    @8
    wceq
    @4
    @1
    @3
    wa
    @11
    @7
    cF
    @3
    @1
    @15
    @11
    @7
    wceq
    @16
    cW
    cN
    @0
    pfxval
    sylan2
    coeq2d
    3adant3
    @5
    @9
    cvv
    wcel
    #
    @15
    wa
    @13
    @10
    wceq
    @5
    @18
    @15
    @5
    cF
    wfun
    #
    @1
    wa
    #
    @18
    @1
    @4
    @20
    @3
    @1
    @4
    wa
    @1
    @19
    @4
    @19
    @1
    cA
    cB
    cF
    ffun
    anim2i
    ancomd
    3adant2
    cF
    cW
    @0
    cofunexg
    syl
    @17
    jca
    @9
    cN
    cvv
    pfxval
    syl
    3eqtr4d
end
