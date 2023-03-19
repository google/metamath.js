include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cmin.mm"
include "cmo.mm"
include "ccsh.mm"
include "caddc.mm"
include "wceq.mm"
include "cn.mm"
include "wa.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "elfzo0.mm"
include "nn0z.mm"
include "3ad2ant1.mm"
include "zsubcl.mm"
include "sylan.mm"
include "simpl2.mm"
include "jca.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"
include "3adant1.mm"
include "zmodfzo.mm"
include "syl.mm"
include "cshwidxmod.mm"
include "syld3an3.mm"
include "cr.mm"
include "crp.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "zred.mm"
include "zre.mm"
include "nnrp.mm"
include "ad3antlr.mm"
include "modaddmod.mm"
include "syl3anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "ad2antrr.mm"
include "zcn.mm"
include "npcan.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "zmodidfzoimp.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "3adant3.mm"
include "pm2.43i.mm"
include "eqtrd.mm"

theorem cshwidxmodr
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( ( W cyclShift N ) ` ( ( I - N ) mod ( # ` W ) ) ) = ( W ` I ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cz
    wcel
    #
    cI
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
    w3a
    #
    cI
    cN
    cmin
    co
    #
    @2
    cmo
    co
    #
    cW
    cN
    ccsh
    co
    cfv
    #
    @7
    cN
    caddc
    co
    @2
    cmo
    co
    #
    cW
    cfv
    #
    cI
    cW
    cfv
    #
    @0
    @1
    @4
    @7
    @3
    wcel
    #
    @8
    @10
    wceq
    @5
    @6
    cz
    wcel
    #
    @2
    cn
    wcel
    #
    wa
    #
    @12
    @1
    @4
    @15
    @0
    @4
    @1
    @15
    @4
    cI
    cn0
    wcel
    #
    @14
    cI
    @2
    clt
    wbr
    #
    w3a
    #
    @1
    @15
    wi
    cI
    @2
    elfzo0
    #
    @18
    @1
    @15
    @18
    @1
    wa
    @13
    @14
    @18
    cI
    cz
    wcel
    #
    @1
    @13
    @16
    @14
    @20
    @17
    cI
    nn0z
    3ad2ant1
    cI
    cN
    zsubcl
    #
    sylan
    @16
    @14
    @17
    @1
    simpl2
    jca
    ex
    sylbi
    impcom
    3adant1
    @6
    @2
    zmodfzo
    syl
    @7
    cN
    cV
    cW
    cshwidxmod
    syld3an3
    @1
    @4
    @10
    @11
    wceq
    #
    @0
    @4
    @1
    @22
    @4
    @1
    @22
    wi
    #
    @4
    @18
    @4
    @23
    wi
    #
    @19
    @16
    @14
    @24
    @17
    @16
    @14
    wa
    #
    @4
    @23
    @25
    @4
    wa
    #
    @1
    @22
    @26
    @1
    wa
    #
    @9
    cI
    cW
    @27
    @9
    @6
    cN
    caddc
    co
    #
    @2
    cmo
    co
    #
    cI
    @2
    cmo
    co
    #
    cI
    @27
    @6
    cr
    wcel
    cN
    cr
    wcel
    #
    @2
    crp
    wcel
    #
    @9
    @29
    wceq
    @27
    @6
    @26
    @20
    @1
    @13
    @4
    @20
    @25
    cI
    cc0
    @2
    elfzoelz
    adantl
    @21
    sylan
    zred
    @1
    @31
    @26
    cN
    zre
    adantl
    @14
    @32
    @16
    @4
    @1
    @2
    nnrp
    ad3antlr
    @6
    cN
    @2
    modaddmod
    syl3anc
    @27
    @28
    cI
    @2
    cmo
    @26
    cI
    cc
    wcel
    #
    cN
    cc
    wcel
    @28
    cI
    wceq
    @1
    @16
    @33
    @14
    @4
    cI
    nn0cn
    ad2antrr
    cN
    zcn
    cI
    cN
    npcan
    syl2an
    oveq1d
    @4
    @30
    cI
    wceq
    @25
    @1
    cI
    @2
    zmodidfzoimp
    ad2antlr
    3eqtrd
    fveq2d
    ex
    ex
    3adant3
    sylbi
    pm2.43i
    impcom
    3adant1
    eqtrd
end
