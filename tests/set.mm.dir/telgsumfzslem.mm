include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "wa.mm"
include "csb.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "csn.mm"
include "cplusg.mm"
include "eqid.mm"
include "ccmn.mm"
include "cabl.mm"
include "adantr.mm"
include "ablcmn.mm"
include "syl.mm"
include "adantl.mm"
include "fzfid.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "ad2antrl.mm"
include "fzelp1.mm"
include "simpr.mm"
include "rspcsbela.mm"
include "syl2anr.mm"
include "fzp1elp1.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "cin.mm"
include "c0.mm"
include "fzp1disj.mm"
include "a1i.mm"
include "cun.mm"
include "fzsuc.mm"
include "gsummptfidmsplit.mm"
include "cvv.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "ovexd.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "syl2an.mm"
include "csbeq1.mm"
include "oveq1.mm"
include "csbeq1d.mm"
include "oveq12d.mm"
include "gsumsnd.mm"
include "eluzfz1.mm"
include "grpnpncan.mm"
include "syl13anc.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem telgsumfzslem
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cC: class C
  let vi: setvar i
  let vk: setvar k
  let cG: class G
  let cM: class M
  let c.mi: class .-
  assume telgsumfzs.b: |- B = ( Base ` G )
  assume telgsumfzs.g: |- ( ph -> G e. Abel )
  assume telgsumfzs.m: |- .- = ( -g ` G )

  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C i
  disjoint G i
  disjoint M i
  disjoint M k
  disjoint .- i
  disjoint i ph
  disjoint i y
  disjoint k y
  assert |- ( ( y e. ( ZZ>= ` M ) /\ ( ph /\ A. k e. ( M ... ( ( y + 1 ) + 1 ) ) C e. B ) ) -> ( ( G gsum ( i e. ( M ... y ) |-> ( [_ i / k ]_ C .- [_ ( i + 1 ) / k ]_ C ) ) ) = ( [_ M / k ]_ C .- [_ ( y + 1 ) / k ]_ C ) -> ( G gsum ( i e. ( M ... ( y + 1 ) ) |-> ( [_ i / k ]_ C .- [_ ( i + 1 ) / k ]_ C ) ) ) = ( [_ M / k ]_ C .- [_ ( ( y + 1 ) + 1 ) / k ]_ C ) ) )

  proof
    vy
    cv
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    cC
    cB
    wcel
    vk
    cM
    @0
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    #
    cG
    vi
    cM
    @0
    cfz
    co
    #
    vk
    vi
    cv
    #
    cC
    csb
    #
    vk
    @10
    c1
    caddc
    co
    #
    cC
    csb
    #
    c.mi
    co
    #
    cmpt
    cgsu
    co
    #
    vk
    cM
    cC
    csb
    #
    vk
    @3
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    cG
    vi
    cM
    @3
    cfz
    co
    #
    @14
    cmpt
    cgsu
    co
    #
    @16
    vk
    @4
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    @8
    @19
    wa
    #
    @21
    @15
    cG
    vi
    @3
    csn
    #
    @14
    cmpt
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @18
    @17
    @22
    c.mi
    co
    #
    @27
    co
    #
    @23
    @8
    @21
    @28
    wceq
    @19
    @8
    @20
    cB
    @9
    @25
    @27
    vi
    cG
    @14
    telgsumfzs.b
    @27
    eqid
    #
    @7
    cG
    ccmn
    wcel
    #
    @2
    @7
    cG
    cabl
    wcel
    #
    @32
    wph
    @33
    @6
    telgsumfzs.g
    adantr
    cG
    ablcmn
    syl
    adantl
    @8
    cM
    @3
    fzfid
    @8
    @10
    @20
    wcel
    #
    wa
    cG
    cgrp
    wcel
    #
    @11
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    @8
    @35
    @34
    wph
    @35
    @2
    @6
    wph
    @33
    @35
    telgsumfzs.g
    cG
    ablgrp
    syl
    #
    ad2antrl
    #
    adantr
    @34
    @10
    @5
    wcel
    @6
    @36
    @8
    @10
    cM
    @3
    fzelp1
    @7
    @6
    @2
    wph
    @6
    simpr
    #
    adantl
    #
    vk
    @10
    @5
    cC
    cB
    rspcsbela
    syl2anr
    @34
    @12
    @5
    wcel
    @6
    @37
    @8
    @10
    cM
    @3
    fzp1elp1
    @41
    vk
    @12
    @5
    cC
    cB
    rspcsbela
    syl2anr
    cB
    cG
    c.mi
    @11
    @13
    telgsumfzs.b
    telgsumfzs.m
    grpsubcl
    syl3anc
    @9
    @25
    cin
    c0
    wceq
    @8
    cM
    @0
    fzp1disj
    a1i
    @2
    @20
    @9
    @25
    cun
    wceq
    @7
    cM
    @0
    fzsuc
    adantr
    gsummptfidmsplit
    adantr
    @24
    @15
    @18
    @26
    @29
    @27
    @8
    @19
    simpr
    @8
    @26
    @29
    wceq
    @19
    @8
    @14
    cB
    @29
    vi
    cG
    @3
    cvv
    telgsumfzs.b
    wph
    cG
    cmnd
    wcel
    #
    @2
    @6
    wph
    @35
    @42
    @38
    cG
    grpmnd
    syl
    ad2antrl
    @8
    @0
    c1
    caddc
    ovexd
    @8
    @35
    @17
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    @29
    cB
    wcel
    @39
    @2
    @3
    @5
    wcel
    #
    @6
    @43
    @7
    @2
    @3
    @20
    wcel
    #
    @45
    @2
    @3
    @1
    wcel
    #
    @46
    cM
    @0
    peano2uz
    #
    cM
    @3
    eluzfz2
    syl
    @3
    cM
    @3
    fzelp1
    syl
    @40
    vk
    @3
    @5
    cC
    cB
    rspcsbela
    syl2an
    #
    @2
    @4
    @5
    wcel
    #
    @6
    @44
    @7
    @2
    @4
    @1
    wcel
    #
    @50
    @2
    @47
    @51
    @48
    cM
    @3
    peano2uz
    syl
    #
    cM
    @4
    eluzfz2
    syl
    @40
    vk
    @4
    @5
    cC
    cB
    rspcsbela
    syl2an
    #
    cB
    cG
    c.mi
    @17
    @22
    telgsumfzs.b
    telgsumfzs.m
    grpsubcl
    syl3anc
    @10
    @3
    wceq
    #
    @14
    @29
    wceq
    @8
    @54
    @11
    @17
    @13
    @22
    c.mi
    vk
    @10
    @3
    cC
    csbeq1
    @54
    vk
    @12
    @4
    cC
    @10
    @3
    c1
    caddc
    oveq1
    csbeq1d
    oveq12d
    adantl
    gsumsnd
    adantr
    oveq12d
    @8
    @30
    @23
    wceq
    #
    @19
    @8
    @35
    @16
    cB
    wcel
    #
    @43
    @44
    @55
    @39
    @2
    cM
    @5
    wcel
    #
    @6
    @56
    @7
    @2
    @51
    @57
    @52
    cM
    @4
    eluzfz1
    syl
    @40
    vk
    cM
    @5
    cC
    cB
    rspcsbela
    syl2an
    @49
    @53
    cB
    @27
    cG
    c.mi
    @16
    @17
    @22
    telgsumfzs.b
    @31
    telgsumfzs.m
    grpnpncan
    syl13anc
    adantr
    3eqtrd
    ex
end
