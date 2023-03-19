include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cfzo.mm"
include "w3a.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "pfxval.mm"
include "sylan2.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "cmin.mm"
include "simp1.mm"
include "0elfz.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "wi.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "a1i.mm"
include "3imp.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "addid1d.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "3eqtrd.mm"

theorem pfxfv
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. ( 0 ... ( # ` W ) ) /\ I e. ( 0 ..^ L ) ) -> ( ( W prefix L ) ` I ) = ( W ` I ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cL
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    cI
    cc0
    cL
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cI
    cW
    cL
    cpfx
    co
    #
    cfv
    cI
    cW
    cc0
    cL
    cop
    csubstr
    co
    #
    cfv
    #
    cI
    cc0
    caddc
    co
    #
    cW
    cfv
    #
    cI
    cW
    cfv
    @6
    cI
    @7
    @8
    @1
    @3
    @7
    @8
    wceq
    #
    @5
    @3
    @1
    cL
    cn0
    wcel
    #
    @12
    cL
    @2
    elfznn0
    #
    cW
    cL
    @0
    pfxval
    sylan2
    3adant3
    fveq1d
    @6
    @1
    cc0
    cc0
    cL
    cfz
    co
    wcel
    #
    @3
    cI
    cc0
    cL
    cc0
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    @9
    @11
    wceq
    @1
    @3
    @5
    simp1
    @3
    @1
    @15
    @5
    @3
    @13
    @15
    @14
    cL
    0elfz
    syl
    3ad2ant2
    @1
    @3
    @5
    simp2
    @1
    @3
    @5
    @18
    @3
    @5
    @18
    wi
    wi
    @1
    @3
    @5
    @18
    @3
    @4
    @17
    cI
    @3
    cL
    @16
    cc0
    cfzo
    @3
    @16
    cL
    @3
    cL
    @3
    cL
    @14
    nn0cnd
    subid1d
    eqcomd
    oveq2d
    eleq2d
    biimpd
    a1i
    3imp
    cV
    cW
    cc0
    cL
    cI
    swrdfv
    syl31anc
    @6
    @10
    cI
    cW
    @5
    @1
    @10
    cI
    wceq
    @3
    @5
    cI
    @5
    cI
    cI
    cc0
    cL
    elfzoelz
    zcnd
    addid1d
    3ad2ant3
    fveq2d
    3eqtrd
end
