include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "c1.mm"
include "ccsh.mm"
include "caddc.mm"
include "cmo.mm"
include "cz.mm"
include "wceq.mm"
include "simpl.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "ubmelm1fzo.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "cc.mm"
include "elfzoel2.mm"
include "zcnd.mm"
include "1cnd.mm"
include "nnpcan.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cn0.mm"
include "cn.mm"
include "w3a.mm"
include "elfzo0.mm"
include "nnre.mm"
include "peano2rem.mm"
include "syl.mm"
include "nnrp.mm"
include "jca.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "nnm1ge0.mm"
include "zre.mm"
include "ltm1d.mm"
include "jca32.mm"
include "modid.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem cshwidxm1
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ..^ ( # ` W ) ) ) -> ( ( W cyclShift N ) ` ( ( ( # ` W ) - N ) - 1 ) ) = ( W ` ( ( # ` W ) - 1 ) ) )

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
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @1
    cN
    cmin
    co
    c1
    cmin
    co
    #
    cW
    cN
    ccsh
    co
    cfv
    #
    @5
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
    @1
    c1
    cmin
    co
    #
    cW
    cfv
    @4
    @0
    cN
    cz
    wcel
    #
    @5
    @2
    wcel
    #
    @6
    @9
    wceq
    @0
    @3
    simpl
    @3
    @11
    @0
    cN
    cc0
    @1
    elfzoelz
    #
    adantl
    @3
    @12
    @0
    cN
    @1
    ubmelm1fzo
    adantl
    @5
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    @4
    @8
    @10
    cW
    @4
    @8
    @10
    @1
    cmo
    co
    #
    @10
    @3
    @8
    @14
    wceq
    @0
    @3
    @7
    @10
    @1
    cmo
    @3
    @1
    cc
    wcel
    cN
    cc
    wcel
    c1
    cc
    wcel
    @7
    @10
    wceq
    @3
    @1
    cN
    cc0
    @1
    elfzoel2
    #
    zcnd
    @3
    cN
    @13
    zcnd
    @3
    1cnd
    @1
    cN
    c1
    nnpcan
    syl3anc
    oveq1d
    adantl
    @4
    @10
    cr
    wcel
    #
    @1
    crp
    wcel
    #
    wa
    #
    cc0
    @10
    cle
    wbr
    #
    @10
    @1
    clt
    wbr
    #
    wa
    wa
    #
    @14
    @10
    wceq
    @3
    @21
    @0
    @3
    @18
    @19
    @20
    @3
    cN
    cn0
    wcel
    #
    @1
    cn
    wcel
    #
    cN
    @1
    clt
    wbr
    #
    w3a
    #
    @18
    cN
    @1
    elfzo0
    #
    @23
    @22
    @18
    @24
    @23
    @16
    @17
    @23
    @1
    cr
    wcel
    @16
    @1
    nnre
    @1
    peano2rem
    syl
    @1
    nnrp
    jca
    3ad2ant2
    sylbi
    @3
    @25
    @19
    @26
    @23
    @22
    @19
    @24
    @1
    nnm1ge0
    3ad2ant2
    sylbi
    @3
    @1
    cz
    wcel
    #
    @20
    @15
    @27
    @1
    @1
    zre
    ltm1d
    syl
    jca32
    adantl
    @10
    @1
    modid
    syl
    eqtrd
    fveq2d
    eqtrd
end
