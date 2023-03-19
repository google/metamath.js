include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "elfz1.mm"
include "bi2anan9.mm"
include "an6.mm"
include "wi.mm"
include "cr.mm"
include "zre.mm"
include "anim12i.mm"
include "le2add.mm"
include "syl2an.mm"
include "impr.mm"
include "3adantr3.mm"
include "adantlr.mm"
include "syl2anr.mm"
include "3adantr2.mm"
include "adantll.mm"
include "wb.mm"
include "zaddcl.mm"
include "elfz.mm"
include "syl3an.mm"
include "3expb.mm"
include "ancoms.mm"
include "3ad2antr1.mm"
include "mpbir2and.mm"
include "ex.mm"
include "an4s.mm"
include "syl5bi.mm"
include "sylbid.mm"

theorem fzadd2
  let cP: class P
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( O e. ZZ /\ P e. ZZ ) ) -> ( ( J e. ( M ... N ) /\ K e. ( O ... P ) ) -> ( J + K ) e. ( ( M + O ) ... ( N + P ) ) ) )

  proof
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
    cO
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    wa
    #
    wa
    #
    cJ
    cM
    cN
    cfz
    co
    wcel
    #
    cK
    cO
    cP
    cfz
    co
    wcel
    #
    wa
    cJ
    cz
    wcel
    #
    cM
    cJ
    cle
    wbr
    #
    cJ
    cN
    cle
    wbr
    #
    w3a
    #
    cK
    cz
    wcel
    #
    cO
    cK
    cle
    wbr
    #
    cK
    cP
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cJ
    cK
    caddc
    co
    #
    cM
    cO
    caddc
    co
    #
    cN
    cP
    caddc
    co
    #
    cfz
    co
    wcel
    #
    @2
    @7
    @12
    @5
    @8
    @16
    cJ
    cM
    cN
    elfz1
    cK
    cO
    cP
    elfz1
    bi2anan9
    @17
    @9
    @13
    wa
    #
    @10
    @14
    wa
    #
    @11
    @15
    wa
    #
    w3a
    #
    @6
    @21
    @9
    @10
    @11
    @13
    @14
    @15
    an6
    @0
    @3
    @1
    @4
    @25
    @21
    wi
    @0
    @3
    wa
    #
    @1
    @4
    wa
    #
    wa
    #
    @25
    @21
    @28
    @25
    wa
    @21
    @19
    @18
    cle
    wbr
    #
    @18
    @20
    cle
    wbr
    #
    @26
    @25
    @29
    @27
    @26
    @22
    @23
    @29
    @24
    @26
    @22
    @23
    @29
    @26
    cM
    cr
    wcel
    #
    cO
    cr
    wcel
    #
    wa
    cJ
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    wa
    #
    @23
    @29
    wi
    @22
    @0
    @31
    @3
    @32
    cM
    zre
    cO
    zre
    anim12i
    @9
    @33
    @13
    @34
    cJ
    zre
    cK
    zre
    anim12i
    #
    cM
    cO
    cJ
    cK
    le2add
    syl2an
    impr
    3adantr3
    adantlr
    @27
    @25
    @30
    @26
    @27
    @22
    @24
    @30
    @23
    @27
    @22
    @24
    @30
    @22
    @35
    cN
    cr
    wcel
    #
    cP
    cr
    wcel
    #
    wa
    @24
    @30
    wi
    @27
    @36
    @1
    @37
    @4
    @38
    cN
    zre
    cP
    zre
    anim12i
    cJ
    cK
    cN
    cP
    le2add
    syl2anr
    impr
    3adantr2
    adantll
    @28
    @23
    @22
    @21
    @29
    @30
    wa
    wb
    #
    @24
    @22
    @28
    @39
    @22
    @26
    @27
    @39
    @22
    @18
    cz
    wcel
    @26
    @19
    cz
    wcel
    @27
    @20
    cz
    wcel
    @39
    cJ
    cK
    zaddcl
    cM
    cO
    zaddcl
    cN
    cP
    zaddcl
    @18
    @19
    @20
    elfz
    syl3an
    3expb
    ancoms
    3ad2antr1
    mpbir2and
    ex
    an4s
    syl5bi
    sylbid
end
