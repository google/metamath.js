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
include "cmin.mm"
include "cfzo.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cn0.mm"
include "wceq.mm"
include "elfznn0.mm"
include "pfxval.mm"
include "sylan2.mm"
include "simpl.mm"
include "adantl.mm"
include "0elfz.mm"
include "syl.mm"
include "simpr.mm"
include "swrdval2.mm"
include "syl3anc.mm"
include "nn0cn.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "elfzonn0.mm"
include "addid1d.mm"
include "fveq2d.mm"
include "mpteq12dva.mm"
include "3eqtrd.mm"

theorem pfxmpt
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cL: class L
  let vl: setvar l
  let vs: setvar s
  let vk: setvar k

  disjoint L x
  disjoint S x
  disjoint A x
  disjoint l s
  disjoint k x
  assert |- ( ( S e. Word A /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S prefix L ) = ( x e. ( 0 ..^ L ) |-> ( S ` x ) ) )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cL
    cc0
    cS
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cS
    cL
    cpfx
    co
    #
    cS
    cc0
    cL
    cop
    csubstr
    co
    #
    vx
    cc0
    cL
    cc0
    cmin
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    vx
    cc0
    cL
    cfzo
    co
    #
    @9
    cS
    cfv
    #
    cmpt
    @3
    @1
    cL
    cn0
    wcel
    #
    @5
    @6
    wceq
    cL
    @2
    elfznn0
    #
    cS
    cL
    @0
    pfxval
    sylan2
    @4
    @1
    cc0
    cc0
    cL
    cfz
    co
    wcel
    #
    @3
    @6
    @12
    wceq
    @1
    @3
    simpl
    @4
    @15
    @17
    @3
    @15
    @1
    @16
    adantl
    cL
    0elfz
    syl
    @1
    @3
    simpr
    vx
    cA
    cS
    cc0
    cL
    swrdval2
    syl3anc
    @4
    vx
    @8
    @11
    @13
    @14
    @3
    @8
    @13
    wceq
    @1
    @3
    @7
    cL
    cc0
    cfzo
    @3
    @15
    @7
    cL
    wceq
    @16
    @15
    cL
    cL
    nn0cn
    subid1d
    syl
    oveq2d
    adantl
    @9
    @8
    wcel
    #
    @11
    @14
    wceq
    @4
    @18
    @10
    @9
    cS
    @18
    @9
    cn0
    wcel
    #
    @10
    @9
    wceq
    @9
    @7
    elfzonn0
    @19
    @9
    @9
    nn0cn
    addid1d
    syl
    fveq2d
    adantl
    mpteq12dva
    3eqtrd
end
