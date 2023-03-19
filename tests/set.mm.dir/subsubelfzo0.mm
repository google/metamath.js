include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "cn0.mm"
include "cn.mm"
include "wi.mm"
include "elfzo0.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "nn0re.mm"
include "adantr.mm"
include "resubcl.mm"
include "syl2anr.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "lenlt.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "nnz.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "ltle.mm"
include "syl2an.mm"
include "impancom.mm"
include "imp.mm"
include "subge0.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "simplr1.mm"
include "nn0sub.mm"
include "mpbid.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "ltsub1d.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "nn0cn.mm"
include "nncan.mm"
include "breq2d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "ex.mm"
include "com3l.mm"
include "3impia.mm"
include "impcom.mm"
include "3jca.mm"
include "exp31.mm"
include "syl5bi.mm"
include "3adant2.mm"
include "sylbi.mm"
include "3imp.mm"
include "elfzo2.mm"
include "sylibr.mm"

theorem subsubelfzo0
  let cA: class A
  let cI: class I
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( 0 ..^ N ) /\ I e. ( 0 ..^ N ) /\ -. I < ( N - A ) ) -> ( I - ( N - A ) ) e. ( 0 ..^ A ) )

  proof
    cA
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cI
    @0
    wcel
    #
    cI
    cN
    cA
    cmin
    co
    #
    clt
    wbr
    wn
    #
    w3a
    cI
    @3
    cmin
    co
    #
    cc0
    cuz
    cfv
    wcel
    #
    cA
    cz
    wcel
    #
    @5
    cA
    clt
    wbr
    #
    w3a
    #
    @5
    cc0
    cA
    cfzo
    co
    wcel
    @1
    @2
    @4
    @9
    @1
    cA
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cA
    cN
    clt
    wbr
    #
    w3a
    @2
    @4
    @9
    wi
    #
    wi
    #
    cA
    cN
    elfzo0
    @10
    @12
    @14
    @11
    @2
    cI
    cn0
    wcel
    #
    @11
    cI
    cN
    clt
    wbr
    #
    w3a
    #
    @10
    @12
    wa
    #
    @13
    cI
    cN
    elfzo0
    @18
    @17
    @4
    @9
    @18
    @17
    wa
    #
    @4
    wa
    #
    @6
    @7
    @8
    @20
    @5
    cn0
    wcel
    #
    @6
    @20
    @3
    cI
    cle
    wbr
    #
    @21
    @19
    @4
    @22
    @19
    @3
    cr
    wcel
    #
    cI
    cr
    wcel
    #
    @4
    @22
    wb
    @17
    cN
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @23
    @18
    @11
    @15
    @25
    @16
    cN
    nnre
    #
    3ad2ant2
    #
    @10
    @26
    @12
    cA
    nn0re
    #
    adantr
    #
    cN
    cA
    resubcl
    #
    syl2anr
    @17
    @24
    @18
    @15
    @11
    @24
    @16
    cI
    nn0re
    #
    3ad2ant1
    adantl
    @23
    @24
    wa
    @22
    @4
    @3
    cI
    lenlt
    bicomd
    syl2anc
    biimpa
    @20
    @3
    cn0
    wcel
    #
    @15
    @22
    @21
    wb
    @19
    @33
    @4
    @19
    @3
    cz
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @33
    @17
    cN
    cz
    wcel
    #
    @7
    @34
    @18
    @11
    @15
    @36
    @16
    cN
    nnz
    3ad2ant2
    @10
    @7
    @12
    cA
    nn0z
    adantr
    #
    cN
    cA
    zsubcl
    syl2anr
    @19
    @35
    cA
    cN
    cle
    wbr
    #
    @18
    @17
    @38
    @10
    @17
    @12
    @38
    @10
    @26
    @25
    @12
    @38
    wi
    @17
    @29
    @28
    cA
    cN
    ltle
    syl2an
    impancom
    imp
    @17
    @25
    @26
    @35
    @38
    wb
    @18
    @28
    @30
    cN
    cA
    subge0
    syl2anr
    mpbird
    @3
    elnn0z
    sylanbrc
    adantr
    @15
    @11
    @16
    @18
    @4
    simplr1
    @3
    cI
    nn0sub
    syl2anc
    mpbid
    @5
    elnn0uz
    sylib
    @19
    @7
    @4
    @18
    @7
    @17
    @37
    adantr
    adantr
    @19
    @8
    @4
    @17
    @18
    @8
    @15
    @11
    @16
    @18
    @8
    wi
    @18
    @15
    @11
    wa
    #
    @16
    @8
    @10
    @39
    @16
    @8
    wi
    #
    wi
    @12
    @10
    @39
    @40
    @10
    @39
    wa
    #
    @16
    @5
    cN
    @3
    cmin
    co
    #
    clt
    wbr
    #
    @8
    @41
    cI
    cN
    @3
    @39
    @24
    @10
    @15
    @24
    @11
    @32
    adantr
    adantl
    @39
    @25
    @10
    @11
    @25
    @15
    @27
    adantl
    #
    adantl
    @39
    @25
    @26
    @23
    @10
    @44
    @29
    @31
    syl2anr
    ltsub1d
    @41
    @43
    @8
    @41
    @42
    cA
    @5
    clt
    @39
    cN
    cc
    wcel
    #
    cA
    cc
    wcel
    @42
    cA
    wceq
    @10
    @11
    @45
    @15
    cN
    nncn
    adantl
    cA
    nn0cn
    cN
    cA
    nncan
    syl2anr
    breq2d
    biimpd
    sylbid
    ex
    adantr
    com3l
    3impia
    impcom
    adantr
    3jca
    exp31
    syl5bi
    3adant2
    sylbi
    3imp
    @5
    cc0
    cA
    elfzo2
    sylibr
end
