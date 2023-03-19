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
include "wceq.mm"
include "caddc.mm"
include "w3a.mm"
include "cmin.mm"
include "simpl.mm"
include "simpr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "adantl.mm"
include "3jca.mm"
include "adantr.mm"
include "cz.mm"
include "elfzelz.mm"
include "zcn.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "swrdswrd.mm"
include "sylc.mm"
include "cc.mm"
include "zcnd.mm"
include "addid2d.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "ex.mm"

theorem swrdswrd0
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) ) -> ( ( K e. ( 0 ... N ) /\ L e. ( K ... N ) ) -> ( ( W substr <. 0 , N >. ) substr <. K , L >. ) = ( W substr <. K , L >. ) ) )

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
    wa
    #
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cL
    cK
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cW
    cc0
    cN
    cop
    csubstr
    co
    cK
    cL
    cop
    #
    csubstr
    co
    #
    cW
    @9
    csubstr
    co
    #
    wceq
    @3
    @8
    wa
    #
    @10
    cW
    cc0
    cK
    caddc
    co
    #
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
    @11
    @12
    @0
    @2
    cc0
    @4
    wcel
    #
    w3a
    #
    cK
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
    cL
    cK
    @19
    cfz
    co
    #
    wcel
    #
    wa
    #
    @10
    @16
    wceq
    @3
    @18
    @8
    @3
    @0
    @2
    @17
    @0
    @2
    simpl
    @0
    @2
    simpr
    @2
    @17
    @0
    @2
    cN
    cn0
    wcel
    @17
    cN
    @1
    elfznn0
    cN
    0elfz
    syl
    adantl
    3jca
    adantr
    @3
    @8
    @24
    @3
    @5
    @21
    @7
    @23
    @3
    @4
    @20
    cK
    @3
    cN
    @19
    cc0
    cfz
    @2
    cN
    @19
    wceq
    #
    @0
    @2
    cN
    cz
    wcel
    #
    @25
    cN
    cc0
    @1
    elfzelz
    @26
    @19
    cN
    @26
    cN
    cN
    zcn
    subid1d
    eqcomd
    syl
    adantl
    #
    oveq2d
    eleq2d
    @3
    @6
    @22
    cL
    @3
    cN
    @19
    cK
    cfz
    @27
    oveq2d
    eleq2d
    anbi12d
    biimpa
    cK
    cL
    cc0
    cN
    cV
    cW
    swrdswrd
    sylc
    @12
    @15
    @9
    cW
    csubstr
    @12
    @13
    cK
    @14
    cL
    @12
    cK
    @8
    cK
    cc
    wcel
    #
    @3
    @5
    @28
    @7
    @5
    cK
    cK
    cc0
    cN
    elfzelz
    zcnd
    adantr
    adantl
    addid2d
    @12
    cL
    @8
    cL
    cc
    wcel
    #
    @3
    @7
    @29
    @5
    @7
    cL
    cL
    cK
    cN
    elfzelz
    zcnd
    adantl
    adantl
    addid2d
    opeq12d
    oveq2d
    eqtrd
    ex
end
