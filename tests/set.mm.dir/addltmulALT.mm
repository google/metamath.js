include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cmul.mm"
include "simpr.mm"
include "wb.mm"
include "2re.mm"
include "a1i.mm"
include "simpl.mm"
include "1re.mm"
include "ltsub1.mm"
include "syl3anc.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "df-2.mm"
include "eqcomi.mm"
include "subaddrii.mm"
include "breq1i.mm"
include "bitrd.mm"
include "mpbid.mm"
include "anim12i.mm"
include "an4s.mm"
include "wi.mm"
include "peano2rem.mm"
include "anim1i.mm"
include "mulgt1.mm"
include "syl.mm"
include "ex.mm"
include "adantr.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "jca.mm"
include "mulsub.mm"
include "breq2d.mm"
include "biimpd.mm"
include "mulid2i.mm"
include "eqcom.mm"
include "biimpi.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "mulid1.mm"
include "adantl.mm"
include "oveq12d.mm"
include "readdcl.mm"
include "remulcl.mm"
include "syl2anc.mm"
include "ltaddsub2.mm"
include "ltadd1.mm"
include "bicomd.mm"
include "sylbird.mm"
include "3syld.mm"
include "mpd.mm"

theorem addltmulALT
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 2 < A /\ 2 < B ) ) -> ( A + B ) < ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    c2
    cA
    clt
    wbr
    #
    c2
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    c1
    cA
    c1
    cmin
    co
    #
    clt
    wbr
    #
    c1
    cB
    c1
    cmin
    co
    #
    clt
    wbr
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @0
    @3
    @1
    @4
    @11
    @0
    @3
    wa
    #
    @8
    @1
    @4
    wa
    #
    @10
    @15
    @3
    @8
    @0
    @3
    simpr
    @15
    @3
    c2
    c1
    cmin
    co
    #
    @7
    clt
    wbr
    #
    @8
    @15
    c2
    cr
    wcel
    #
    @0
    c1
    cr
    wcel
    #
    @3
    @18
    wb
    @19
    @15
    2re
    a1i
    @0
    @3
    simpl
    @20
    @15
    1re
    a1i
    c2
    cA
    c1
    ltsub1
    syl3anc
    @18
    @8
    wb
    @15
    @17
    c1
    @7
    clt
    c2
    c1
    c1
    2cn
    ax-1cn
    ax-1cn
    c2
    c1
    c1
    caddc
    co
    df-2
    eqcomi
    subaddrii
    #
    breq1i
    a1i
    bitrd
    mpbid
    @16
    @4
    @10
    @1
    @4
    simpr
    @16
    @4
    @17
    @9
    clt
    wbr
    #
    @10
    @16
    @19
    @1
    @20
    @4
    @22
    wb
    @19
    @16
    2re
    a1i
    @1
    @4
    simpl
    @20
    @16
    1re
    a1i
    c2
    cB
    c1
    ltsub1
    syl3anc
    @22
    @10
    wb
    @16
    @17
    c1
    @9
    clt
    @21
    breq1i
    a1i
    bitrd
    mpbid
    anim12i
    an4s
    @6
    @11
    c1
    @7
    @9
    cmul
    co
    #
    clt
    wbr
    #
    c1
    @13
    c1
    c1
    cmul
    co
    #
    caddc
    co
    #
    cA
    c1
    cmul
    co
    #
    cB
    c1
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    @14
    @2
    @11
    @24
    wi
    @5
    @2
    @11
    @24
    @2
    @11
    wa
    @7
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wa
    #
    @11
    wa
    @24
    @2
    @34
    @11
    @0
    @32
    @1
    @33
    cA
    peano2rem
    cB
    peano2rem
    anim12i
    anim1i
    @7
    @9
    mulgt1
    syl
    ex
    adantr
    @2
    @24
    @31
    wi
    @5
    @2
    @24
    @31
    @2
    @23
    @30
    c1
    clt
    @2
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    wa
    #
    cB
    cc
    wcel
    #
    @36
    wa
    #
    wa
    @23
    @30
    wceq
    @0
    @37
    @1
    @39
    @0
    @35
    @36
    cA
    recn
    #
    @36
    @0
    ax-1cn
    a1i
    jca
    @1
    @38
    @36
    cB
    recn
    #
    @36
    @1
    ax-1cn
    a1i
    jca
    anim12i
    cA
    c1
    cB
    c1
    mulsub
    syl
    breq2d
    biimpd
    adantr
    @2
    @31
    @14
    wi
    @5
    @2
    @31
    c1
    @13
    c1
    caddc
    co
    #
    @12
    cmin
    co
    #
    clt
    wbr
    #
    @14
    @2
    @43
    @30
    c1
    clt
    @2
    @42
    @26
    @12
    @29
    cmin
    @2
    c1
    @25
    @13
    caddc
    @25
    c1
    wceq
    #
    c1
    @25
    wceq
    #
    @2
    c1
    ax-1cn
    mulid2i
    @45
    @46
    @25
    c1
    eqcom
    biimpi
    mp1i
    oveq2d
    @2
    cA
    @27
    cB
    @28
    caddc
    @0
    cA
    @27
    wceq
    #
    @1
    @0
    @35
    @47
    @40
    @35
    @27
    cA
    wceq
    #
    @47
    cA
    mulid1
    @48
    @47
    @27
    cA
    eqcom
    biimpi
    syl
    syl
    adantr
    @1
    cB
    @28
    wceq
    #
    @0
    @1
    @28
    cB
    wceq
    #
    @49
    @1
    @38
    @50
    @41
    cB
    mulid1
    syl
    @50
    @49
    @28
    cB
    eqcom
    biimpi
    syl
    adantl
    oveq12d
    oveq12d
    breq2d
    @2
    @44
    @12
    c1
    caddc
    co
    @42
    clt
    wbr
    #
    @14
    @2
    @12
    cr
    wcel
    #
    @20
    @42
    cr
    wcel
    #
    @51
    @44
    wb
    cA
    cB
    readdcl
    #
    @20
    @2
    1re
    a1i
    #
    @2
    @13
    cr
    wcel
    #
    @20
    @53
    cA
    cB
    remulcl
    #
    @55
    @13
    c1
    readdcl
    syl2anc
    @12
    c1
    @42
    ltaddsub2
    syl3anc
    @2
    @51
    @14
    @2
    @14
    @51
    @2
    @52
    @56
    @20
    @14
    @51
    wb
    @54
    @57
    @55
    @12
    @13
    c1
    ltadd1
    syl3anc
    bicomd
    biimpd
    sylbird
    sylbird
    adantr
    3syld
    mpd
end
