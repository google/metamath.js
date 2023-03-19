include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cfzo.mm"
include "wn.mm"
include "caddc.mm"
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
include "elfzoelz.mm"
include "wb.mm"
include "elfzelz.mm"
include "simpl.mm"
include "anim12i.mm"
include "simpr.mm"
include "anim12ci.mm"
include "jca.mm"
include "exp32.mm"
include "syl5.mm"
include "imp.mm"
include "impcom.mm"
include "elfzomelpfzo.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "simpl3.mm"
include "simpl2.mm"
include "adantl.mm"
include "3jca.mm"
include "eluz2.mm"
include "sylibr.mm"
include "fzoss2.mm"
include "sseld.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "mpcom.mm"
include "com12.mm"
include "syld.mm"

theorem swrdccatin12lem2a
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X


  assert |- ( ( M e. ( 0 ... L ) /\ N e. ( L ... X ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> ( K + M ) e. ( L ..^ X ) ) )

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
    wcel
    #
    cK
    cM
    caddc
    co
    #
    cL
    cX
    cfzo
    co
    #
    wcel
    #
    @2
    @4
    cz
    wcel
    #
    @5
    @6
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
    wa
    #
    wa
    #
    @10
    cM
    cc0
    cL
    elfz2
    #
    @14
    @10
    @15
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
    @3
    cK
    cc0
    @4
    elfzonelfzo
    syl
    @6
    @2
    @9
    cK
    cz
    wcel
    #
    @6
    @2
    @9
    wi
    cK
    @4
    @3
    elfzoelz
    @18
    @2
    @6
    @9
    @18
    @2
    @6
    @9
    wi
    @18
    @2
    wa
    #
    @6
    @7
    cL
    cN
    cfzo
    co
    #
    wcel
    #
    @9
    @19
    @12
    cN
    cz
    wcel
    #
    wa
    #
    @18
    @13
    wa
    #
    wa
    #
    @6
    @21
    wb
    @2
    @18
    @25
    @0
    @1
    @18
    @25
    wi
    #
    @0
    @16
    @1
    @26
    wi
    #
    @17
    @14
    @27
    @15
    @12
    @13
    @27
    @11
    @1
    @22
    @12
    @13
    wa
    #
    @26
    cN
    cL
    cX
    elfzelz
    @28
    @22
    @18
    @25
    @28
    @22
    @18
    wa
    #
    wa
    @23
    @24
    @28
    @12
    @29
    @22
    @12
    @13
    simpl
    @22
    @18
    simpl
    anim12i
    @28
    @13
    @29
    @18
    @12
    @13
    simpr
    @22
    @18
    simpr
    anim12ci
    jca
    exp32
    syl5
    3adant1
    adantr
    sylbi
    imp
    impcom
    cK
    cM
    cL
    cN
    elfzomelpfzo
    syl
    @19
    @20
    @8
    @7
    @19
    cX
    cN
    cuz
    cfv
    wcel
    #
    @20
    @8
    wss
    @19
    @22
    cX
    cz
    wcel
    #
    cN
    cX
    cle
    wbr
    #
    w3a
    #
    @30
    @2
    @33
    @18
    @1
    @33
    @0
    @1
    @12
    @31
    @22
    w3a
    #
    cL
    cN
    cle
    wbr
    #
    @32
    wa
    #
    wa
    #
    @33
    cN
    cL
    cX
    elfz2
    @37
    @22
    @31
    @32
    @12
    @31
    @22
    @36
    simpl3
    @12
    @31
    @22
    @36
    simpl2
    @36
    @32
    @34
    @35
    @32
    simpr
    adantl
    3jca
    sylbi
    adantl
    adantl
    cN
    cX
    eluz2
    sylibr
    cN
    cL
    cX
    fzoss2
    syl
    sseld
    sylbid
    ex
    com23
    mpcom
    com12
    syld
end
