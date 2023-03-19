include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cneg.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "cn.mm"
include "w3a.mm"
include "wi.mm"
include "elfzo0.mm"
include "caddc.mm"
include "cr.mm"
include "cle.mm"
include "nn0re.mm"
include "adantr.mm"
include "nnre.mm"
include "resubcl.mm"
include "syl2an.mm"
include "ancoms.mm"
include "3adant3.mm"
include "anim12i.mm"
include "nn0ge0.mm"
include "wb.mm"
include "posdif.mm"
include "biimp3a.mm"
include "addgegt0.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "subadd23d.mm"
include "breqtrrd.mm"
include "possumd.mm"
include "mpbid.mm"
include "readdcl.mm"
include "3jca.mm"
include "addge02.mm"
include "syl.mm"
include "lelttrdi.mm"
include "impancom.mm"
include "imp.mm"
include "ltsubadd2d.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "syl5bi.mm"
include "3adant2.mm"
include "sylbi.mm"

theorem subfzo0
  let cI: class I
  let cJ: class J
  let cN: class N


  assert |- ( ( I e. ( 0 ..^ N ) /\ J e. ( 0 ..^ N ) ) -> ( -u N < ( I - J ) /\ ( I - J ) < N ) )

  proof
    cI
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cJ
    @0
    wcel
    #
    cN
    cneg
    cI
    cJ
    cmin
    co
    #
    clt
    wbr
    #
    @3
    cN
    clt
    wbr
    #
    wa
    #
    @1
    cI
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cI
    cN
    clt
    wbr
    #
    w3a
    @2
    @6
    wi
    #
    cI
    cN
    elfzo0
    @7
    @9
    @10
    @8
    @2
    cJ
    cn0
    wcel
    #
    @8
    cJ
    cN
    clt
    wbr
    #
    w3a
    #
    @7
    @9
    wa
    #
    @6
    cJ
    cN
    elfzo0
    @14
    @13
    @6
    @14
    @13
    wa
    #
    @4
    @5
    @15
    cc0
    @3
    cN
    caddc
    co
    #
    clt
    wbr
    @4
    @15
    cc0
    cI
    cN
    cJ
    cmin
    co
    #
    caddc
    co
    #
    @16
    clt
    @15
    cI
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    wa
    cc0
    cI
    cle
    wbr
    #
    cc0
    @17
    clt
    wbr
    #
    wa
    cc0
    @18
    clt
    wbr
    @14
    @19
    @13
    @20
    @7
    @19
    @9
    cI
    nn0re
    #
    adantr
    #
    @11
    @8
    @20
    @12
    @8
    @11
    @20
    @8
    cN
    cr
    wcel
    #
    cJ
    cr
    wcel
    #
    @20
    @11
    cN
    nnre
    #
    cJ
    nn0re
    #
    cN
    cJ
    resubcl
    syl2an
    ancoms
    3adant3
    anim12i
    @14
    @21
    @13
    @22
    @7
    @21
    @9
    cI
    nn0ge0
    adantr
    @11
    @8
    @12
    @22
    @11
    @26
    @25
    @12
    @22
    wb
    @8
    @28
    @27
    cJ
    cN
    posdif
    syl2an
    biimp3a
    anim12i
    cI
    @17
    addgegt0
    syl2anc
    @15
    cI
    cJ
    cN
    @14
    cI
    cc
    wcel
    #
    @13
    @7
    @29
    @9
    cI
    nn0cn
    adantr
    adantr
    @13
    cJ
    cc
    wcel
    #
    @14
    @11
    @8
    @30
    @12
    cJ
    nn0cn
    3ad2ant1
    adantl
    @13
    cN
    cc
    wcel
    #
    @14
    @8
    @11
    @31
    @12
    cN
    nncn
    3ad2ant2
    adantl
    subadd23d
    breqtrrd
    @15
    @3
    cN
    @14
    @19
    @26
    @3
    cr
    wcel
    @13
    @24
    @11
    @8
    @26
    @12
    @28
    3ad2ant1
    #
    cI
    cJ
    resubcl
    syl2an
    @13
    @25
    @14
    @8
    @11
    @25
    @12
    @27
    3ad2ant2
    #
    adantl
    #
    possumd
    mpbid
    @15
    @5
    cI
    cJ
    cN
    caddc
    co
    #
    clt
    wbr
    #
    @14
    @13
    @36
    @7
    @13
    @9
    @36
    @7
    @13
    wa
    #
    cI
    cN
    @35
    @37
    @19
    @25
    @35
    cr
    wcel
    #
    @7
    @19
    @13
    @23
    adantr
    @13
    @25
    @7
    @33
    adantl
    @13
    @38
    @7
    @11
    @8
    @38
    @12
    @11
    @26
    @25
    @38
    @8
    @28
    @27
    cJ
    cN
    readdcl
    syl2an
    3adant3
    adantl
    3jca
    @37
    cc0
    cJ
    cle
    wbr
    #
    cN
    @35
    cle
    wbr
    #
    @13
    @39
    @7
    @11
    @8
    @39
    @12
    cJ
    nn0ge0
    3ad2ant1
    adantl
    @37
    @25
    @26
    wa
    #
    @39
    @40
    wb
    @13
    @41
    @7
    @11
    @8
    @41
    @12
    @8
    @11
    @41
    @8
    @25
    @11
    @26
    @27
    @28
    anim12i
    ancoms
    3adant3
    adantl
    cN
    cJ
    addge02
    syl
    mpbid
    lelttrdi
    impancom
    imp
    @15
    cI
    cJ
    cN
    @14
    @19
    @13
    @24
    adantr
    @13
    @26
    @14
    @32
    adantl
    @34
    ltsubadd2d
    mpbird
    jca
    ex
    syl5bi
    3adant2
    sylbi
    imp
end
