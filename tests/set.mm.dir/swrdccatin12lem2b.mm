include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cfzo.mm"
include "wn.mm"
include "cz.mm"
include "wi.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "elfz2.mm"
include "zsubcl.mm"
include "3adant1.mm"
include "adantr.mm"
include "sylbi.mm"
include "elfzonelfzo.mm"
include "syl.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "elfz2nn0.mm"
include "cc.mm"
include "nn0cn.mm"
include "elfzelz.mm"
include "zcn.mm"
include "subcl.mm"
include "ancoms.mm"
include "addid1d.mm"
include "eqcomd.mm"
include "adantl.mm"
include "simprr.mm"
include "simpl.mm"
include "npncan3d.mm"
include "subid1.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "ex.mm"
include "3syl.mm"
include "com12.mm"
include "syl2an.mm"
include "3adant3.mm"
include "imp.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "0zd.mm"
include "zsubcld.mm"
include "3adant2.mm"
include "3jca.mm"
include "fzosubel2.mm"
include "syl2anc.mm"
include "syld.mm"

theorem swrdccatin12lem2b
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X


  assert |- ( ( M e. ( 0 ... L ) /\ N e. ( L ... X ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> ( K - ( L - M ) ) e. ( 0 ..^ ( ( N - L ) - 0 ) ) ) )

  proof
    cM
    cc0
    cL
    cfz
    co
    wcel
    #
    cN
    cL
    cX
    cfz
    co
    wcel
    #
    wa
    #
    cK
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    cK
    cc0
    cL
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    wn
    wa
    #
    cK
    @4
    @3
    cfzo
    co
    #
    wcel
    #
    cK
    @4
    cmin
    co
    cc0
    cN
    cL
    cmin
    co
    #
    cc0
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    @2
    @4
    cz
    wcel
    #
    @5
    @7
    wi
    @0
    @11
    @1
    @0
    cc0
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cc0
    cM
    cle
    wbr
    cM
    cL
    cle
    wbr
    #
    wa
    #
    wa
    @11
    cM
    cc0
    cL
    elfz2
    @15
    @11
    @17
    @13
    @14
    @11
    @12
    cL
    cM
    zsubcl
    3adant1
    adantr
    sylbi
    adantr
    #
    @3
    cK
    cc0
    @4
    elfzonelfzo
    syl
    @2
    @7
    @10
    @2
    @7
    wa
    cK
    @4
    cc0
    caddc
    co
    #
    @4
    @9
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @11
    @12
    @9
    cz
    wcel
    #
    w3a
    #
    @10
    @2
    @7
    @22
    @2
    @6
    @21
    cK
    @0
    @1
    @6
    @21
    wceq
    #
    @0
    cM
    cn0
    wcel
    #
    cL
    cn0
    wcel
    #
    @16
    w3a
    @1
    @25
    wi
    #
    cM
    cL
    elfz2nn0
    @26
    @27
    @28
    @16
    @26
    cM
    cc
    wcel
    #
    cL
    cc
    wcel
    #
    @28
    @27
    cM
    nn0cn
    cL
    nn0cn
    @1
    @29
    @30
    wa
    #
    @25
    @1
    cN
    cz
    wcel
    #
    cN
    cc
    wcel
    #
    @31
    @25
    wi
    cN
    cL
    cX
    elfzelz
    cN
    zcn
    @33
    @31
    @25
    @33
    @31
    wa
    #
    @4
    @19
    @3
    @20
    cfzo
    @31
    @4
    @19
    wceq
    @33
    @31
    @19
    @4
    @31
    @4
    @30
    @29
    @4
    cc
    wcel
    cL
    cM
    subcl
    ancoms
    addid1d
    eqcomd
    adantl
    @34
    @4
    @8
    caddc
    co
    @3
    @20
    @34
    cL
    cM
    cN
    @33
    @29
    @30
    simprr
    @31
    @29
    @33
    @29
    @30
    simpl
    adantl
    @33
    @31
    simpl
    npncan3d
    @34
    @8
    @9
    @4
    caddc
    @33
    @30
    @8
    @9
    wceq
    #
    @29
    @33
    @30
    wa
    @8
    cc
    wcel
    #
    @35
    cN
    cL
    subcl
    @36
    @9
    @8
    @8
    subid1
    eqcomd
    syl
    adantrl
    oveq2d
    eqtr3d
    oveq12d
    ex
    3syl
    com12
    syl2an
    3adant3
    sylbi
    imp
    eleq2d
    biimpa
    @2
    @24
    @7
    @2
    @11
    @12
    @23
    @18
    @2
    0zd
    @1
    @23
    @0
    @1
    @13
    cX
    cz
    wcel
    #
    @32
    w3a
    #
    cL
    cN
    cle
    wbr
    cN
    cX
    cle
    wbr
    wa
    #
    wa
    @23
    cN
    cL
    cX
    elfz2
    @38
    @23
    @39
    @13
    @32
    @23
    @37
    @13
    @32
    wa
    #
    @8
    cc0
    @32
    @13
    @8
    cz
    wcel
    cN
    cL
    zsubcl
    ancoms
    @40
    0zd
    zsubcld
    3adant2
    adantr
    sylbi
    adantl
    3jca
    adantr
    cK
    @4
    cc0
    @9
    fzosubel2
    syl2anc
    ex
    syld
end
