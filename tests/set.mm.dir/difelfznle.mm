include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "caddc.mm"
include "cmin.mm"
include "cn0.mm"
include "cz.mm"
include "elfz2nn0.mm"
include "wa.mm"
include "nn0addcl.mm"
include "nn0zd.mm"
include "3adant3.mm"
include "sylbi.mm"
include "elfzelz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "cr.mm"
include "zred.mm"
include "adantr.mm"
include "elfzel2.mm"
include "nn0readdcl.mm"
include "adantl.mm"
include "elfzle2.mm"
include "elfzle1.mm"
include "wb.mm"
include "nn0re.mm"
include "anim12ci.mm"
include "addge02.mm"
include "syl.mm"
include "mpbid.mm"
include "anim12i.mm"
include "letr.mm"
include "imp.mm"
include "syl31anc.mm"
include "zre.mm"
include "readdcl.mm"
include "sylan.mm"
include "subge0.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "elfz3nn0.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "clt.mm"
include "ltnle.mm"
include "ancoms.mm"
include "ltle.mm"
include "sylbird.mm"
include "syl2an.mm"
include "3impia.mm"
include "leadd1d.mm"
include "lesubadd2d.mm"
include "syl3anbrc.mm"

theorem difelfznle
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( 0 ... N ) /\ M e. ( 0 ... N ) /\ -. K <_ M ) -> ( ( M + N ) - K ) e. ( 0 ... N ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cM
    @0
    wcel
    #
    cK
    cM
    cle
    wbr
    wn
    #
    w3a
    #
    cM
    cN
    caddc
    co
    #
    cK
    cmin
    co
    #
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @6
    cN
    cle
    wbr
    #
    @6
    @0
    wcel
    @4
    @6
    cz
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @7
    @1
    @2
    @10
    @3
    @2
    @5
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @10
    @1
    @2
    cM
    cn0
    wcel
    #
    @8
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @12
    cM
    cN
    elfz2nn0
    #
    @14
    @8
    @12
    @15
    @14
    @8
    wa
    @5
    cM
    cN
    nn0addcl
    nn0zd
    3adant3
    sylbi
    cK
    cc0
    cN
    elfzelz
    #
    @5
    cK
    zsubcl
    syl2anr
    3adant3
    @4
    @11
    cK
    @5
    cle
    wbr
    #
    @1
    @2
    @19
    @3
    @1
    @2
    wa
    #
    cK
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    cN
    @5
    cle
    wbr
    #
    wa
    #
    @19
    @1
    @21
    @2
    @1
    cK
    @18
    zred
    adantr
    #
    @1
    @22
    @2
    @1
    cN
    cK
    cc0
    cN
    elfzel2
    zred
    adantr
    #
    @2
    @23
    @1
    @2
    @16
    @23
    @17
    @14
    @8
    @23
    @15
    cM
    cN
    nn0readdcl
    3adant3
    sylbi
    adantl
    #
    @1
    @24
    @2
    @25
    cK
    cc0
    cN
    elfzle2
    @2
    cc0
    cM
    cle
    wbr
    #
    @25
    cM
    cc0
    cN
    elfzle1
    @2
    @22
    cM
    cr
    wcel
    #
    wa
    #
    @30
    @25
    wb
    @2
    @16
    @32
    @17
    @14
    @8
    @32
    @15
    @14
    @31
    @8
    @22
    cM
    nn0re
    #
    cN
    nn0re
    #
    anim12ci
    3adant3
    sylbi
    cN
    cM
    addge02
    syl
    mpbid
    anim12i
    @21
    @22
    @23
    w3a
    @26
    @19
    cK
    cN
    @5
    letr
    imp
    syl31anc
    3adant3
    @4
    @23
    @21
    wa
    #
    @11
    @19
    wb
    @1
    @2
    @35
    @3
    @1
    @13
    @2
    @35
    @18
    @13
    @21
    @2
    @23
    cK
    zre
    #
    @2
    @31
    @22
    wa
    #
    @23
    @2
    @16
    @37
    @17
    @14
    @8
    @37
    @15
    @14
    @31
    @8
    @22
    @33
    @34
    anim12i
    3adant3
    sylbi
    cM
    cN
    readdcl
    syl
    anim12ci
    sylan
    3adant3
    @5
    cK
    subge0
    syl
    mpbird
    @6
    elnn0z
    sylanbrc
    @1
    @2
    @8
    @3
    cK
    cN
    elfz3nn0
    3ad2ant1
    @4
    @9
    @5
    cK
    cN
    caddc
    co
    cle
    wbr
    #
    @4
    cM
    cK
    cle
    wbr
    #
    @38
    @1
    @2
    @3
    @39
    @1
    @13
    cM
    cz
    wcel
    #
    @3
    @39
    wi
    #
    @2
    @18
    cM
    cc0
    cN
    elfzelz
    #
    @13
    @21
    @31
    @41
    @40
    @36
    cM
    zre
    @21
    @31
    wa
    @3
    cM
    cK
    clt
    wbr
    #
    @39
    @31
    @21
    @43
    @3
    wb
    cM
    cK
    ltnle
    ancoms
    @31
    @21
    @43
    @39
    wi
    cM
    cK
    ltle
    ancoms
    sylbird
    syl2an
    syl2an
    3impia
    @1
    @2
    @39
    @38
    wb
    @3
    @20
    cM
    cK
    cN
    @2
    @31
    @1
    @2
    cM
    @42
    zred
    adantl
    @27
    @28
    leadd1d
    3adant3
    mpbid
    @1
    @2
    @9
    @38
    wb
    @3
    @20
    @5
    cK
    cN
    @29
    @27
    @28
    lesubadd2d
    3adant3
    mpbird
    @6
    cN
    elfz2nn0
    syl3anbrc
end
