include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cfzo.mm"
include "caddc.mm"
include "wi.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "elfz2nn0.mm"
include "wa.mm"
include "cn.mm"
include "clt.mm"
include "elfzo0.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "znnsub.mm"
include "syl2an.mm"
include "simpr.mm"
include "simpll.mm"
include "nn0addcl.mm"
include "syl2anr.mm"
include "adantr.mm"
include "cr.mm"
include "0red.mm"
include "nn0re.mm"
include "adantl.mm"
include "3jca.mm"
include "nn0ge0.mm"
include "anim1i.mm"
include "lelttr.mm"
include "sylc.mm"
include "ex.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "syl.mm"
include "syld.mm"
include "exp4b.mm"
include "com24.mm"
include "imp.mm"
include "com13.mm"
include "readdcl.mm"
include "ltaddsubd.mm"
include "exbiri.mm"
include "com23.mm"
include "impd.mm"
include "anasss.mm"
include "syl3anbrc.mm"
include "exp53.mm"
include "sylbird.mm"
include "3adant3.mm"
include "com14.mm"
include "3imp.mm"
include "sylbi.mm"
include "3adant1.mm"
include "com12.mm"

theorem elfzodifsumelfzo
  let cP: class P
  let cI: class I
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ( 0 ... N ) /\ N e. ( 0 ... P ) ) -> ( I e. ( 0 ..^ ( N - M ) ) -> ( I + M ) e. ( 0 ..^ P ) ) )

  proof
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    cP
    cfz
    co
    wcel
    #
    cI
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cI
    cM
    caddc
    co
    #
    cc0
    cP
    cfzo
    co
    wcel
    #
    wi
    #
    @0
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @1
    @6
    wi
    cM
    cN
    elfz2nn0
    @1
    @10
    @6
    @1
    @8
    cP
    cn0
    wcel
    #
    cN
    cP
    cle
    wbr
    #
    w3a
    @10
    @6
    wi
    #
    cN
    cP
    elfz2nn0
    @11
    @12
    @13
    @8
    @3
    @10
    @11
    @12
    wa
    #
    @5
    @3
    cI
    cn0
    wcel
    #
    @2
    cn
    wcel
    #
    cI
    @2
    clt
    wbr
    #
    w3a
    @10
    @14
    @5
    wi
    #
    wi
    #
    cI
    @2
    elfzo0
    @15
    @16
    @17
    @19
    @10
    @16
    @17
    @15
    @18
    @7
    @8
    @16
    @17
    @15
    @18
    wi
    wi
    #
    wi
    @9
    @7
    @8
    wa
    #
    @16
    cM
    cN
    clt
    wbr
    #
    @20
    @7
    cM
    cz
    wcel
    cN
    cz
    wcel
    @22
    @16
    wb
    @8
    cM
    nn0z
    cN
    nn0z
    cM
    cN
    znnsub
    syl2an
    @21
    @22
    @17
    @15
    @14
    @5
    @21
    @22
    wa
    #
    @17
    @15
    wa
    #
    wa
    #
    @14
    wa
    @4
    cn0
    wcel
    #
    cP
    cn
    wcel
    #
    @4
    cP
    clt
    wbr
    #
    @5
    @25
    @26
    @14
    @24
    @15
    @7
    @26
    @23
    @17
    @15
    simpr
    @7
    @8
    @22
    simpll
    cI
    cM
    nn0addcl
    syl2anr
    adantr
    @25
    @14
    @27
    @23
    @14
    @27
    wi
    #
    @24
    @21
    @22
    @29
    @21
    @22
    cc0
    cN
    clt
    wbr
    #
    @29
    @21
    @22
    @30
    @23
    cc0
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    cc0
    cM
    cle
    wbr
    #
    @22
    wa
    @30
    @21
    @34
    @22
    @21
    @31
    @32
    @33
    @21
    0red
    @7
    @32
    @8
    cM
    nn0re
    adantr
    #
    @8
    @33
    @7
    cN
    nn0re
    #
    adantl
    #
    3jca
    adantr
    @21
    @35
    @22
    @7
    @35
    @8
    cM
    nn0ge0
    adantr
    anim1i
    cc0
    cM
    cN
    lelttr
    sylc
    ex
    @8
    @30
    @29
    wi
    @7
    @14
    @30
    @8
    @27
    @11
    @12
    @30
    @8
    @27
    wi
    wi
    @11
    @8
    @30
    @12
    @27
    @11
    @8
    @30
    @12
    @27
    @11
    @8
    wa
    #
    @30
    @12
    wa
    #
    cc0
    cP
    clt
    wbr
    #
    @27
    @39
    @31
    @33
    cP
    cr
    wcel
    #
    @40
    @41
    wi
    @39
    0red
    @8
    @33
    @11
    @37
    adantl
    @11
    @42
    @8
    cP
    nn0re
    #
    adantr
    cc0
    cN
    cP
    ltletr
    syl3anc
    @11
    @41
    @27
    wi
    #
    @8
    @11
    cP
    cz
    wcel
    #
    @44
    cP
    nn0z
    @27
    @45
    @41
    cP
    elnnz
    simplbi2
    syl
    adantr
    syld
    exp4b
    com24
    imp
    com13
    adantl
    syld
    imp
    adantr
    imp
    @25
    @11
    @12
    @28
    @25
    @11
    wa
    #
    @12
    wa
    @4
    cr
    wcel
    #
    @33
    @42
    w3a
    #
    @4
    cN
    clt
    wbr
    #
    @12
    wa
    @28
    @46
    @48
    @12
    @46
    @47
    @33
    @42
    @25
    @47
    @11
    @24
    cI
    cr
    wcel
    #
    @32
    @47
    @23
    @15
    @50
    @17
    cI
    nn0re
    #
    adantl
    @21
    @32
    @22
    @36
    adantr
    cI
    cM
    readdcl
    syl2anr
    adantr
    @25
    @33
    @11
    @23
    @33
    @24
    @21
    @33
    @22
    @38
    adantr
    adantr
    adantr
    @11
    @42
    @25
    @43
    adantl
    3jca
    adantr
    @46
    @49
    @12
    @25
    @49
    @11
    @23
    @24
    @49
    @21
    @24
    @49
    wi
    @22
    @21
    @17
    @15
    @49
    @21
    @15
    @17
    @49
    @21
    @15
    @49
    @17
    @21
    @15
    wa
    cI
    cM
    cN
    @15
    @50
    @21
    @51
    adantl
    @21
    @32
    @15
    @36
    adantr
    @21
    @33
    @15
    @38
    adantr
    ltaddsubd
    exbiri
    com23
    impd
    adantr
    imp
    adantr
    anim1i
    @4
    cN
    cP
    ltletr
    sylc
    anasss
    @4
    cP
    elfzo0
    syl3anbrc
    exp53
    sylbird
    3adant3
    com14
    3imp
    sylbi
    com13
    3adant1
    sylbi
    com12
    sylbi
    imp
end
