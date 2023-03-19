include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "cn0.mm"
include "wa.mm"
include "wceq.mm"
include "elfznn0.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pfxval.mm"
include "syl.mm"
include "oveq1d.mm"
include "cmin.mm"
include "simp1.mm"
include "simp2.mm"
include "0elfz.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "pfxswrd.mm"
include "sylc.mm"
include "addid2d.mm"
include "opeq2d.mm"
include "3ad2ant3.mm"
include "3adant2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem pfxpfx
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) /\ L e. ( 0 ... N ) ) -> ( ( W prefix N ) prefix L ) = ( W prefix L ) )

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
    cW
    cN
    cpfx
    co
    #
    cL
    cpfx
    co
    cW
    cc0
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
    cc0
    cc0
    cL
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    cL
    cpfx
    co
    #
    @6
    @7
    @8
    cL
    cpfx
    @6
    @1
    cN
    cn0
    wcel
    #
    wa
    #
    @7
    @8
    wceq
    @1
    @3
    @15
    @5
    @3
    @14
    @1
    cN
    @2
    elfznn0
    #
    anim2i
    3adant3
    cW
    cN
    @0
    pfxval
    syl
    oveq1d
    @6
    @1
    @3
    cc0
    @4
    wcel
    #
    w3a
    cL
    cc0
    cN
    cc0
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @9
    @12
    wceq
    @6
    @1
    @3
    @17
    @1
    @3
    @5
    simp1
    @1
    @3
    @5
    simp2
    @3
    @1
    @17
    @5
    @3
    @14
    @17
    @16
    cN
    0elfz
    syl
    3ad2ant2
    3jca
    @1
    @3
    @5
    @20
    @1
    @3
    wa
    #
    @4
    @19
    cL
    @21
    cN
    @18
    cc0
    cfz
    @3
    cN
    @18
    wceq
    @1
    @3
    @18
    cN
    @3
    cN
    @3
    cN
    @16
    nn0cnd
    subid1d
    eqcomd
    adantl
    oveq2d
    eleq2d
    biimp3a
    cL
    cc0
    cN
    cV
    cW
    pfxswrd
    sylc
    @6
    @12
    cW
    cc0
    cL
    cop
    #
    csubstr
    co
    #
    @13
    @5
    @1
    @12
    @23
    wceq
    @3
    @5
    @11
    @22
    cW
    csubstr
    @5
    @10
    cL
    cc0
    @5
    cL
    @5
    cL
    cL
    cN
    elfznn0
    #
    nn0cnd
    addid2d
    opeq2d
    oveq2d
    3ad2ant3
    @6
    @1
    cL
    cn0
    wcel
    #
    wa
    #
    @13
    @23
    wceq
    @1
    @5
    @26
    @3
    @5
    @25
    @1
    @24
    anim2i
    3adant2
    cW
    cL
    @0
    pfxval
    syl
    eqtr4d
    3eqtrd
end
