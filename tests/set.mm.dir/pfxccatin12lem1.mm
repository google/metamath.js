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
include "3adant2.mm"
include "3jca.mm"
include "fzosubel2.mm"
include "syl2anc.mm"
include "syld.mm"

theorem pfxccatin12lem1
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. ( 0 ... L ) /\ N e. ( L ... X ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> ( K - ( L - M ) ) e. ( 0 ..^ ( N - L ) ) ) )

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
    @10
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
    @10
    cM
    cc0
    cL
    elfz2
    @14
    @10
    @16
    @12
    @13
    @10
    @11
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
    @9
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
    @8
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @10
    @11
    @8
    cz
    wcel
    #
    w3a
    #
    @9
    @2
    @7
    @21
    @2
    @6
    @20
    cK
    @0
    @1
    @6
    @20
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
    @15
    w3a
    @1
    @24
    wi
    #
    cM
    cL
    elfz2nn0
    @25
    @26
    @27
    @15
    @25
    cM
    cc
    wcel
    #
    cL
    cc
    wcel
    #
    @27
    @26
    cM
    nn0cn
    cL
    nn0cn
    @1
    @28
    @29
    wa
    #
    @24
    @1
    cN
    cz
    wcel
    #
    cN
    cc
    wcel
    #
    @30
    @24
    wi
    cN
    cL
    cX
    elfzelz
    cN
    zcn
    @32
    @30
    @24
    @32
    @30
    wa
    #
    @4
    @18
    @3
    @19
    cfzo
    @30
    @4
    @18
    wceq
    @32
    @30
    @18
    @4
    @30
    @4
    @29
    @28
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
    @33
    @19
    @3
    @33
    cL
    cM
    cN
    @32
    @28
    @29
    simprr
    @30
    @28
    @32
    @28
    @29
    simpl
    adantl
    @32
    @30
    simpl
    npncan3d
    eqcomd
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
    @23
    @7
    @2
    @10
    @11
    @22
    @17
    @2
    0zd
    @1
    @22
    @0
    @1
    @12
    cX
    cz
    wcel
    #
    @31
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
    @22
    cN
    cL
    cX
    elfz2
    @35
    @22
    @36
    @12
    @31
    @22
    @34
    @31
    @12
    @22
    cN
    cL
    zsubcl
    ancoms
    3adant2
    adantr
    sylbi
    adantl
    3jca
    adantr
    cK
    @4
    cc0
    @8
    fzosubel2
    syl2anc
    ex
    syld
end
