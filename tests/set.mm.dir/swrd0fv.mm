include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cfzo.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "simp1.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "wa.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "subid1.mm"
include "eqcomd.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "elfzoelz.mm"
include "addid1d.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem swrd0fv
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ L e. ( 0 ... ( # ` W ) ) /\ I e. ( 0 ..^ L ) ) -> ( ( W substr <. 0 , L >. ) ` I ) = ( W ` I ) )

  proof
    cW
    cV
    cword
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
    cc0
    cL
    cop
    csubstr
    co
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
    @5
    @0
    cc0
    cc0
    cL
    cfz
    co
    wcel
    #
    @2
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
    @6
    @8
    wceq
    @0
    @2
    @4
    simp1
    @2
    @0
    @9
    @4
    @2
    cL
    cn0
    wcel
    @9
    cL
    @1
    elfznn0
    cL
    0elfz
    syl
    3ad2ant2
    @0
    @2
    @4
    simp2
    @0
    @2
    @4
    @12
    @0
    @2
    wa
    #
    @3
    @11
    cI
    @13
    cL
    @10
    cc0
    cfzo
    @2
    cL
    @10
    wceq
    #
    @0
    @2
    cL
    cc
    wcel
    #
    @14
    @2
    cL
    cL
    cc0
    @1
    elfzelz
    zcnd
    @15
    @10
    cL
    cL
    subid1
    eqcomd
    syl
    adantl
    oveq2d
    eleq2d
    biimp3a
    cV
    cW
    cc0
    cL
    cI
    swrdfv
    syl31anc
    @5
    @7
    cI
    cW
    @4
    @0
    @7
    cI
    wceq
    @2
    @4
    cI
    @4
    cI
    cI
    cc0
    cL
    elfzoelz
    zcnd
    addid1d
    3ad2ant3
    fveq2d
    eqtrd
end
