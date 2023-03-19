include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "wss.mm"
include "cle.mm"
include "wi.mm"
include "df-3an.mm"
include "biimpri.mm"
include "3adant2.mm"
include "ssfzo12.mm"
include "syl.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "simprrl.mm"
include "adantr.mm"
include "simpll.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "letr.mm"
include "syl3anc.mm"
include "imp.mm"
include "3jca.mm"
include "exp31.mm"
include "com23.mm"
include "expdimp.mm"
include "impancom.mm"
include "com13.mm"
include "3adant3.mm"
include "com12.mm"
include "impcom.mm"
include "sylibr.mm"
include "simpl2r.mm"
include "ad3antlr.mm"
include "ltletr.mm"
include "ex.mm"
include "expcomd.mm"
include "adantld.mm"
include "syl3anbrc.mm"
include "3adant1.mm"
include "sylbi.mm"
include "ssrdv.mm"
include "impbid.mm"

theorem ssfzo12bi
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( ( K e. ZZ /\ L e. ZZ ) /\ ( M e. ZZ /\ N e. ZZ ) /\ K < L ) -> ( ( K ..^ L ) C_ ( M ..^ N ) <-> ( M <_ K /\ L <_ N ) ) )

  proof
    cK
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    wa
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cK
    cL
    clt
    wbr
    #
    w3a
    #
    cK
    cL
    cfzo
    co
    #
    cM
    cN
    cfzo
    co
    #
    wss
    #
    cM
    cK
    cle
    wbr
    #
    cL
    cN
    cle
    wbr
    #
    wa
    #
    @7
    @0
    @1
    @6
    w3a
    #
    @10
    @13
    wi
    @2
    @6
    @14
    @5
    @14
    @2
    @6
    wa
    @0
    @1
    @6
    df-3an
    biimpri
    3adant2
    cK
    cL
    cM
    cN
    ssfzo12
    syl
    @7
    @13
    @10
    @7
    @13
    wa
    #
    vx
    @8
    @9
    vx
    cv
    #
    @8
    wcel
    #
    @15
    @16
    @9
    wcel
    #
    @17
    @16
    cK
    cuz
    cfv
    wcel
    #
    @1
    @16
    cL
    clt
    wbr
    #
    w3a
    @15
    @18
    wi
    #
    @16
    cK
    cL
    elfzo2
    @19
    @20
    @21
    @1
    @19
    @20
    @21
    @19
    @0
    @16
    cz
    wcel
    #
    cK
    @16
    cle
    wbr
    #
    w3a
    @20
    @21
    wi
    #
    cK
    @16
    eluz2
    @22
    @23
    @24
    @0
    @22
    @23
    wa
    #
    @20
    @15
    @18
    @25
    @20
    wa
    #
    @15
    wa
    #
    @16
    cM
    cuz
    cfv
    wcel
    #
    @4
    @16
    cN
    clt
    wbr
    #
    @18
    @27
    @3
    @22
    cM
    @16
    cle
    wbr
    #
    w3a
    #
    @28
    @26
    @15
    @31
    @25
    @15
    @31
    wi
    @20
    @15
    @25
    @31
    @13
    @7
    @25
    @31
    wi
    #
    @11
    @7
    @32
    wi
    @12
    @7
    @11
    @32
    @2
    @5
    @11
    @32
    wi
    @6
    @25
    @11
    @2
    @5
    wa
    #
    @31
    @22
    @11
    @23
    @33
    @31
    wi
    #
    @22
    @11
    @23
    @34
    @22
    @33
    @11
    @23
    wa
    #
    @31
    @22
    @33
    @35
    @31
    @22
    @33
    wa
    #
    @35
    wa
    @3
    @22
    @30
    @36
    @3
    @35
    @22
    @2
    @3
    @4
    simprrl
    adantr
    @22
    @33
    @35
    simpll
    @36
    @35
    @30
    @36
    cM
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @35
    @30
    wi
    @33
    @37
    @22
    @5
    @37
    @2
    @3
    @37
    @4
    cM
    zre
    adantr
    adantl
    adantl
    @33
    @38
    @22
    @2
    @38
    @5
    @0
    @38
    @1
    cK
    zre
    adantr
    adantr
    adantl
    @22
    @39
    @33
    @16
    zre
    #
    adantr
    cM
    cK
    @16
    letr
    syl3anc
    imp
    3jca
    exp31
    com23
    expdimp
    impancom
    com13
    3adant3
    com12
    adantr
    impcom
    com12
    adantr
    imp
    cM
    @16
    eluz2
    sylibr
    @15
    @4
    @26
    @3
    @4
    @2
    @6
    @13
    simpl2r
    adantl
    @26
    @15
    @29
    @25
    @20
    @15
    @29
    wi
    #
    @22
    @20
    @41
    wi
    @23
    @15
    @20
    @22
    @29
    @7
    @13
    @20
    @22
    @29
    wi
    #
    wi
    #
    @7
    @12
    @43
    @11
    @7
    @20
    @12
    @42
    @2
    @5
    @20
    @12
    wa
    #
    @42
    wi
    @6
    @33
    @22
    @44
    @29
    @33
    @22
    @44
    @29
    wi
    #
    @33
    @22
    wa
    @39
    cL
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @45
    @22
    @39
    @33
    @40
    adantl
    @1
    @46
    @0
    @5
    @22
    cL
    zre
    ad3antlr
    @33
    @47
    @22
    @5
    @47
    @2
    @4
    @47
    @3
    cN
    zre
    adantl
    adantl
    adantr
    @16
    cL
    cN
    ltletr
    syl3anc
    ex
    com23
    3adant3
    expcomd
    adantld
    imp
    com13
    adantr
    imp
    imp
    @16
    cM
    cN
    elfzo2
    syl3anbrc
    exp31
    3adant1
    sylbi
    imp
    3adant2
    sylbi
    com12
    ssrdv
    ex
    impbid
end
