include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "ccsh.mm"
include "caddc.mm"
include "cmo.mm"
include "cc0.mm"
include "cz.mm"
include "cfzo.mm"
include "wceq.mm"
include "simpl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ubmelfzo.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "cc.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "elfz1b.mm"
include "nncn.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "sylbi.mm"
include "npcan.mm"
include "syl.mm"
include "oveq1d.mm"
include "crp.mm"
include "nnrp.mm"
include "modid0.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem cshwidxm
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 1 ... ( # ` W ) ) ) -> ( ( W cyclShift N ) ` ( ( # ` W ) - N ) ) = ( W ` 0 ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    c1
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
    @1
    cN
    cmin
    co
    #
    cW
    cN
    ccsh
    co
    cfv
    #
    @4
    cN
    caddc
    co
    #
    @1
    cmo
    co
    #
    cW
    cfv
    #
    cc0
    cW
    cfv
    @3
    @0
    cN
    cz
    wcel
    #
    @4
    cc0
    @1
    cfzo
    co
    wcel
    #
    @5
    @8
    wceq
    @0
    @2
    simpl
    @2
    @9
    @0
    cN
    c1
    @1
    elfzelz
    adantl
    @2
    @10
    @0
    cN
    @1
    ubmelfzo
    adantl
    @4
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    @3
    @7
    cc0
    cW
    @3
    @7
    @1
    @1
    cmo
    co
    #
    cc0
    @2
    @7
    @11
    wceq
    @0
    @2
    @6
    @1
    @1
    cmo
    @2
    @1
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    wa
    #
    @6
    @1
    wceq
    @2
    cN
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    cN
    @1
    cle
    wbr
    #
    w3a
    #
    @14
    @1
    cN
    elfz1b
    #
    @15
    @16
    @14
    @17
    @15
    @13
    @16
    @12
    cN
    nncn
    @1
    nncn
    anim12ci
    3adant3
    sylbi
    @1
    cN
    npcan
    syl
    oveq1d
    adantl
    @2
    @11
    cc0
    wceq
    #
    @0
    @2
    @18
    @20
    @19
    @16
    @15
    @20
    @17
    @16
    @1
    crp
    wcel
    @20
    @1
    nnrp
    @1
    modid0
    syl
    3ad2ant2
    sylbi
    adantl
    eqtrd
    fveq2d
    eqtrd
end
