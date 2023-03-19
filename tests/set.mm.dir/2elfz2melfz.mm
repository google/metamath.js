include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cn0.mm"
include "cle.mm"
include "cz.mm"
include "wi.mm"
include "elfzelz.mm"
include "elfzel2.mm"
include "simplr.mm"
include "zsubcl.mm"
include "adantlr.mm"
include "zsubcld.mm"
include "adantr.mm"
include "cr.mm"
include "zre.mm"
include "ad2antrr.mm"
include "zaddcl.mm"
include "zred.mm"
include "expcom.mm"
include "adantl.mm"
include "imp.mm"
include "ltsub1d.mm"
include "anim12i.mm"
include "id.mm"
include "resubcld.mm"
include "readdcl.mm"
include "simpll.mm"
include "jca.mm"
include "ltle.mm"
include "3syl.mm"
include "wceq.mm"
include "zcn.mm"
include "subidd.mm"
include "cc.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "subsub3.mm"
include "eqtr4d.mm"
include "syl3anc.mm"
include "breq12d.mm"
include "sylibd.mm"
include "sylbid.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "exp31.mm"
include "syl2anc.mm"
include "mpan9.mm"
include "elfznn0.mm"
include "elfzle2.mm"
include "zcnd.mm"
include "npcan.mm"
include "syl.mm"
include "breqtrrd.mm"
include "lesubadd2d.mm"
include "mpbird.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "ex.mm"

theorem 2elfz2melfz
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( 0 ... N ) /\ B e. ( 0 ... N ) ) -> ( N < ( A + B ) -> ( B - ( N - A ) ) e. ( 0 ... A ) ) )

  proof
    cA
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cN
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    #
    cB
    cN
    cA
    cmin
    co
    #
    cmin
    co
    #
    cc0
    cA
    cfz
    co
    wcel
    #
    @3
    @5
    wa
    @7
    cn0
    wcel
    #
    cA
    cn0
    wcel
    #
    @7
    cA
    cle
    wbr
    #
    @8
    @3
    @5
    @9
    @1
    cA
    cz
    wcel
    #
    @2
    @5
    @9
    wi
    #
    cA
    cc0
    cN
    elfzelz
    #
    @2
    cN
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @12
    @13
    wi
    cB
    cc0
    cN
    elfzel2
    cB
    cc0
    cN
    elfzelz
    #
    @15
    @16
    wa
    #
    @12
    @5
    @9
    @18
    @12
    wa
    #
    @5
    wa
    @7
    cz
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @9
    @19
    @20
    @5
    @19
    cB
    @6
    @15
    @16
    @12
    simplr
    @15
    @12
    @6
    cz
    wcel
    @16
    cN
    cA
    zsubcl
    adantlr
    zsubcld
    adantr
    @19
    @5
    @21
    @19
    @5
    cN
    cN
    cmin
    co
    #
    @4
    cN
    cmin
    co
    #
    clt
    wbr
    #
    @21
    @19
    cN
    @4
    cN
    @15
    cN
    cr
    wcel
    #
    @16
    @12
    cN
    zre
    #
    ad2antrr
    #
    @18
    @12
    @4
    cr
    wcel
    #
    @16
    @12
    @28
    wi
    @15
    @12
    @16
    @28
    @12
    @16
    wa
    @4
    cA
    cB
    zaddcl
    zred
    expcom
    adantl
    imp
    @27
    ltsub1d
    @19
    @24
    @22
    @23
    cle
    wbr
    #
    @21
    @19
    @25
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    wa
    #
    @22
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    wa
    @24
    @29
    wi
    @18
    @31
    @12
    @32
    @15
    @25
    @16
    @30
    @26
    cB
    zre
    anim12i
    cA
    zre
    anim12i
    @33
    @34
    @35
    @25
    @34
    @30
    @32
    @25
    cN
    cN
    @25
    id
    #
    @36
    resubcld
    ad2antrr
    @33
    @4
    cN
    @31
    @32
    @28
    @30
    @32
    @28
    wi
    @25
    @32
    @30
    @28
    cA
    cB
    readdcl
    expcom
    adantl
    imp
    @25
    @30
    @32
    simpll
    resubcld
    jca
    @22
    @23
    ltle
    3syl
    @19
    @22
    cc0
    @23
    @7
    cle
    @15
    @22
    cc0
    wceq
    @16
    @12
    @15
    cN
    cN
    zcn
    #
    subidd
    ad2antrr
    @19
    cB
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @23
    @7
    wceq
    @18
    @38
    @12
    @16
    @38
    @15
    cB
    zcn
    adantl
    adantr
    @15
    @39
    @16
    @12
    @37
    ad2antrr
    @12
    @40
    @18
    cA
    zcn
    adantl
    @38
    @39
    @40
    w3a
    #
    @23
    cB
    cA
    caddc
    co
    #
    cN
    cmin
    co
    @7
    @41
    @4
    @42
    cN
    cmin
    @41
    cA
    cB
    @38
    @39
    @40
    simp3
    @38
    @39
    @40
    simp1
    addcomd
    oveq1d
    cB
    cN
    cA
    subsub3
    eqtr4d
    syl3anc
    breq12d
    sylibd
    sylbid
    imp
    @7
    elnn0z
    sylanbrc
    exp31
    syl2anc
    mpan9
    imp
    @1
    @10
    @2
    @5
    cA
    cN
    elfznn0
    ad2antrr
    @3
    @11
    @5
    @3
    @11
    cB
    @6
    cA
    caddc
    co
    #
    cle
    wbr
    @3
    cB
    cN
    @43
    cle
    @2
    cB
    cN
    cle
    wbr
    @1
    cB
    cc0
    cN
    elfzle2
    adantl
    @3
    @39
    @40
    wa
    #
    @43
    cN
    wceq
    @1
    @44
    @2
    @1
    @39
    @40
    @1
    cN
    cA
    cc0
    cN
    elfzel2
    #
    zcnd
    @1
    cA
    @14
    zcnd
    jca
    adantr
    cN
    cA
    npcan
    syl
    breqtrrd
    @3
    cB
    @6
    cA
    @2
    @30
    @1
    @2
    cB
    @17
    zred
    adantl
    @1
    @6
    cr
    wcel
    @2
    @1
    cN
    cA
    @1
    cN
    @45
    zred
    @1
    cA
    @14
    zred
    #
    resubcld
    adantr
    @1
    @32
    @2
    @46
    adantr
    lesubadd2d
    mpbird
    adantr
    @7
    cA
    elfz2nn0
    syl3anbrc
    ex
end
