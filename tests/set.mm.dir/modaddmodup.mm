include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cfzo.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cmul.mm"
include "clt.mm"
include "elfzoelz.mm"
include "zred.mm"
include "adantr.mm"
include "zmodcl.mm"
include "nn0red.mm"
include "adantl.mm"
include "readdcld.mm"
include "ancoms.mm"
include "nnrp.mm"
include "ad2antlr.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "wi.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "nnre.mm"
include "zre.mm"
include "lesubaddd.mm"
include "biimpd.mm"
include "impancom.mm"
include "3adant1.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "eluzelz.mm"
include "anim12i.mm"
include "jca.mm"
include "simpr.mm"
include "modlt.mm"
include "syl2an.mm"
include "ltled.mm"
include "ltleadd.mm"
include "sylc.mm"
include "nncn.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "exp31.mm"
include "com23.mm"
include "syl.mm"
include "imp.mm"
include "3adant2.mm"
include "2submod.mm"
include "eqcomd.mm"
include "syl22anc.mm"
include "modadd2mod.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "ex.mm"

theorem modaddmodup
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. ZZ /\ M e. NN ) -> ( B e. ( ( M - ( A mod M ) ) ..^ M ) -> ( ( B + ( A mod M ) ) - M ) = ( ( B + A ) mod M ) ) )

  proof
    cA
    cz
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    cB
    cM
    cA
    cM
    cmo
    co
    #
    cmin
    co
    #
    cM
    cfzo
    co
    wcel
    #
    cB
    @3
    caddc
    co
    #
    cM
    cmin
    co
    #
    cB
    cA
    caddc
    co
    cM
    cmo
    co
    #
    wceq
    @2
    @5
    wa
    #
    @7
    @6
    cM
    cmo
    co
    #
    @8
    @9
    @6
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    cM
    @6
    cle
    wbr
    #
    @6
    c2
    cM
    cmul
    co
    #
    clt
    wbr
    #
    @7
    @10
    wceq
    @5
    @2
    @11
    @5
    @2
    wa
    cB
    @3
    @5
    cB
    cr
    wcel
    #
    @2
    @5
    cB
    cB
    @4
    cM
    elfzoelz
    zred
    #
    adantr
    @2
    @3
    cr
    wcel
    #
    @5
    @2
    @3
    cA
    cM
    zmodcl
    nn0red
    #
    adantl
    readdcld
    ancoms
    @1
    @12
    @0
    @5
    cM
    nnrp
    #
    ad2antlr
    #
    @5
    @2
    @13
    @5
    cB
    @4
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cB
    cM
    clt
    wbr
    #
    w3a
    #
    @2
    @13
    wi
    #
    cB
    @4
    cM
    elfzo2
    #
    @22
    @23
    @26
    @24
    @22
    @4
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @4
    cB
    cle
    wbr
    #
    w3a
    @26
    @4
    cB
    eluz2
    @29
    @30
    @26
    @28
    @29
    @2
    @30
    @13
    @29
    @2
    wa
    #
    @30
    @13
    @31
    cM
    @3
    cB
    @2
    cM
    cr
    wcel
    #
    @29
    @1
    @32
    @0
    cM
    nnre
    #
    adantl
    #
    adantl
    @2
    @18
    @29
    @19
    adantl
    @29
    @16
    @2
    cB
    zre
    #
    adantr
    lesubaddd
    biimpd
    impancom
    3adant1
    sylbi
    3ad2ant1
    sylbi
    impcom
    @5
    @2
    @15
    @5
    @25
    @2
    @15
    wi
    #
    @27
    @22
    @24
    @36
    @23
    @22
    @24
    @36
    @22
    @29
    @24
    @36
    wi
    @4
    cB
    eluzelz
    @29
    @2
    @24
    @15
    @29
    @2
    @24
    @15
    @31
    @24
    wa
    #
    @6
    cM
    cM
    caddc
    co
    #
    @14
    clt
    @37
    @16
    @18
    wa
    #
    @32
    @32
    wa
    #
    wa
    #
    @24
    @3
    cM
    cle
    wbr
    #
    wa
    @6
    @38
    clt
    wbr
    @31
    @41
    @24
    @31
    @39
    @40
    @29
    @16
    @2
    @18
    @35
    @19
    anim12i
    @2
    @40
    @29
    @1
    @40
    @0
    @1
    @32
    @32
    @33
    @33
    jca
    adantl
    adantl
    jca
    adantr
    @37
    @24
    @42
    @31
    @24
    simpr
    @2
    @42
    @29
    @24
    @2
    @3
    cM
    @19
    @34
    @0
    cA
    cr
    wcel
    #
    @12
    @3
    cM
    clt
    wbr
    @1
    cA
    zre
    #
    @20
    cA
    cM
    modlt
    syl2an
    ltled
    ad2antlr
    jca
    cB
    @3
    cM
    cM
    ltleadd
    sylc
    @2
    @14
    @38
    wceq
    #
    @29
    @24
    @1
    @45
    @0
    @1
    cM
    cM
    nncn
    2timesd
    adantl
    ad2antlr
    breqtrrd
    exp31
    com23
    syl
    imp
    3adant2
    sylbi
    impcom
    @11
    @12
    wa
    @13
    @15
    wa
    wa
    @10
    @7
    @6
    cM
    2submod
    eqcomd
    syl22anc
    @9
    @43
    @16
    @12
    @10
    @8
    wceq
    @2
    @43
    @5
    @0
    @43
    @1
    @44
    adantr
    adantr
    @5
    @16
    @2
    @17
    adantl
    @21
    cA
    cB
    cM
    modadd2mod
    syl3anc
    eqtrd
    ex
end
