include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "meaf.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "xaddid2.mm"
include "syl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "uneq1.mm"
include "0un.mm"
include "a1i.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "fveq2.mm"
include "mea0.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "cin.mm"
include "ad2antrr.mm"
include "inidm.mm"
include "eqcomi.mm"
include "ineq2.mm"
include "syl5req.mm"
include "neqne.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "adantll.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "cpr.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "uniprg.mm"
include "syl2anc.mm"
include "prssd.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "prfi.mm"
include "csdm.mm"
include "isfinite.mm"
include "biimpi.mm"
include "sdomdom.mm"
include "ax-mp.mm"
include "cv.mm"
include "wdisj.mm"
include "csn.mm"
include "disjxsn.mm"
include "preq1.mm"
include "dfsn2.mm"
include "disjeq1d.mm"
include "mpbird.mm"
include "wb.mm"
include "simpr.mm"
include "id.mm"
include "disjprg.mm"
include "syl3anc.mm"
include "pm2.61dan.mm"
include "meadjuni.mm"
include "cmpt.mm"
include "sge0pr.mm"
include "fssresd.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem meadjun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vk: setvar k
  assume meadjun.m: |- ( ph -> M e. Meas )
  assume meadjun.x: |- S = dom M
  assume meadjun.a: |- ( ph -> A e. S )
  assume meadjun.b: |- ( ph -> B e. S )
  assume meadjun.dj: |- ( ph -> ( A i^i B ) = (/) )


  assert |- ( ph -> ( M ` ( A u. B ) ) = ( ( M ` A ) +e ( M ` B ) ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    cun
    #
    cM
    cfv
    #
    cA
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    cxad
    co
    #
    wceq
    #
    wph
    @0
    wa
    #
    @4
    cc0
    @4
    cxad
    co
    #
    @2
    @5
    wph
    @4
    @8
    wceq
    @0
    wph
    @8
    @4
    wph
    @4
    cxr
    wcel
    @8
    @4
    wceq
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @4
    cc0
    cpnf
    iccssxr
    wph
    cS
    @9
    cB
    cM
    wph
    cS
    cM
    meadjun.m
    meadjun.x
    meaf
    #
    meadjun.b
    ffvelrnd
    #
    sseldi
    @4
    xaddid2
    syl
    eqcomd
    adantr
    @0
    @2
    @4
    wceq
    wph
    @0
    @1
    cB
    cM
    @0
    @1
    c0
    cB
    cun
    #
    cB
    cA
    c0
    cB
    uneq1
    @12
    cB
    wceq
    @0
    cB
    0un
    a1i
    eqtrd
    fveq2d
    adantl
    @7
    @3
    cc0
    @4
    cxad
    @7
    @3
    c0
    cM
    cfv
    #
    cc0
    @0
    @3
    @13
    wceq
    wph
    cA
    c0
    cM
    fveq2
    adantl
    wph
    @13
    cc0
    wceq
    @0
    wph
    cM
    meadjun.m
    mea0
    adantr
    eqtrd
    oveq1d
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    wph
    cA
    cB
    wne
    #
    @6
    wph
    @14
    simpl
    @15
    cA
    cB
    @15
    cA
    cB
    wceq
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    wph
    @19
    @14
    @17
    meadjun.dj
    ad2antrr
    @14
    @17
    @19
    wn
    wph
    @14
    @17
    wa
    #
    @18
    c0
    @20
    @18
    cA
    c0
    @17
    @18
    cA
    wceq
    @14
    @17
    cA
    cA
    cA
    cin
    #
    @18
    @21
    cA
    cA
    inidm
    eqcomi
    cA
    cB
    cA
    ineq2
    syl5req
    adantl
    @14
    cA
    c0
    wne
    @17
    cA
    c0
    neqne
    adantr
    eqnetrd
    neneqd
    adantll
    pm2.65da
    neqned
    wph
    @16
    wa
    #
    @2
    cA
    cB
    cpr
    #
    cuni
    #
    cM
    cfv
    #
    cM
    @23
    cres
    #
    csumge0
    cfv
    #
    @5
    wph
    @2
    @25
    wceq
    @16
    wph
    @1
    @24
    cM
    wph
    @24
    @1
    wph
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @24
    @1
    wceq
    meadjun.a
    meadjun.b
    cA
    cB
    cS
    cS
    uniprg
    syl2anc
    eqcomd
    fveq2d
    adantr
    wph
    @25
    @27
    wceq
    @16
    wph
    vx
    cS
    cM
    @23
    meadjun.m
    meadjun.x
    wph
    cA
    cB
    cS
    meadjun.a
    meadjun.b
    prssd
    #
    @23
    com
    cdom
    wbr
    #
    wph
    @23
    cfn
    wcel
    #
    @31
    cA
    cB
    prfi
    @32
    @23
    com
    csdm
    wbr
    #
    @31
    @32
    @33
    @23
    isfinite
    biimpi
    @23
    com
    sdomdom
    syl
    ax-mp
    a1i
    wph
    @17
    vx
    @23
    vx
    cv
    #
    wdisj
    #
    @17
    @35
    wph
    @17
    @35
    vx
    cB
    csn
    #
    @34
    wdisj
    #
    @37
    @17
    vx
    cB
    @34
    disjxsn
    a1i
    @17
    vx
    @23
    @36
    @34
    @17
    @23
    cB
    cB
    cpr
    #
    @36
    cA
    cB
    cB
    preq1
    @38
    @36
    wceq
    @17
    @36
    @38
    cB
    dfsn2
    eqcomi
    a1i
    eqtrd
    disjeq1d
    mpbird
    adantl
    wph
    @17
    wn
    #
    wa
    wph
    @16
    @35
    wph
    @39
    simpl
    @39
    @16
    wph
    cA
    cB
    neqne
    adantl
    @22
    @35
    @19
    wph
    @19
    @16
    meadjun.dj
    adantr
    @22
    @28
    @29
    @16
    @35
    @19
    wb
    wph
    @28
    @16
    meadjun.a
    adantr
    #
    wph
    @29
    @16
    meadjun.b
    adantr
    #
    wph
    @16
    simpr
    #
    vx
    cA
    cB
    @34
    cA
    cB
    cS
    @34
    cA
    wceq
    id
    @34
    cB
    wceq
    id
    disjprg
    syl3anc
    mpbird
    syl2anc
    pm2.61dan
    meadjuni
    adantr
    @22
    vx
    @23
    @34
    cM
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @5
    @27
    @5
    @22
    cA
    cB
    @43
    @3
    vx
    @4
    cS
    cS
    @40
    @41
    wph
    @3
    @9
    wcel
    @16
    wph
    cS
    @9
    cA
    cM
    @10
    meadjun.a
    ffvelrnd
    adantr
    wph
    @4
    @9
    wcel
    @16
    @11
    adantr
    @34
    cA
    cM
    fveq2
    @34
    cB
    cM
    fveq2
    @42
    sge0pr
    wph
    @27
    @45
    wceq
    @16
    wph
    @26
    @44
    csumge0
    wph
    @26
    vx
    @23
    @34
    @26
    cfv
    #
    cmpt
    #
    @44
    wph
    vx
    @23
    @9
    @26
    wph
    cS
    @9
    @23
    cM
    @10
    @30
    fssresd
    feqmptd
    @47
    @44
    wceq
    wph
    vx
    @23
    @46
    @43
    @34
    @23
    cM
    fvres
    mpteq2ia
    a1i
    eqtrd
    fveq2d
    adantr
    @22
    @5
    eqidd
    3eqtr4d
    3eqtrd
    syl2anc
    pm2.61dan
end
