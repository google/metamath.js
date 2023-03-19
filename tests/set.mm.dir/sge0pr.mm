include "cpnf.mm"
include "wceq.mm"
include "cpr.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "cc0.mm"
include "cicc.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "mnfxr.mm"
include "a1i.mm"
include "0xr.mm"
include "clt.mm"
include "wbr.mm"
include "mnflt0.mm"
include "cle.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xrltletrd.mm"
include "xrgtned.mm"
include "xaddpnf2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "adantr.mm"
include "cvv.mm"
include "prex.mm"
include "wf.mm"
include "cv.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "simpl.mm"
include "neqne.mm"
include "elprn1.mm"
include "adantll.mm"
include "pm2.61dan.mm"
include "eqid.mm"
include "fmptd.mm"
include "crn.mm"
include "id.mm"
include "prid1g.mm"
include "syl.mm"
include "rnmptpr.mm"
include "eleqtrd.mm"
include "sge0pnfval.mm"
include "oveq1.mm"
include "3eqtr4d.mm"
include "xaddpnf1.mm"
include "prid2g.mm"
include "oveq2.mm"
include "csu.mm"
include "caddc.mm"
include "cc.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "pnfge.mm"
include "necon3bi.mm"
include "xrleneltd.mm"
include "elicod.mm"
include "jca.mm"
include "ad2antrr.mm"
include "sumpr.mm"
include "cfn.mm"
include "prfi.mm"
include "ad4ant14.mm"
include "simp-4l.mm"
include "simpllr.mm"
include "w3a.mm"
include "3adant2.mm"
include "3adant3.mm"
include "sge0fsummpt.mm"
include "rexadd.mm"

theorem sge0pr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume sge0pr.a: |- ( ph -> A e. V )
  assume sge0pr.b: |- ( ph -> B e. W )
  assume sge0pr.d: |- ( ph -> D e. ( 0 [,] +oo ) )
  assume sge0pr.e: |- ( ph -> E e. ( 0 [,] +oo ) )
  assume sge0pr.cd: |- ( k = A -> C = D )
  assume sge0pr.ce: |- ( k = B -> C = E )
  assume sge0pr.ab: |- ( ph -> A =/= B )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint E k
  disjoint V k
  disjoint W k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. { A , B } |-> C ) ) = ( D +e E ) )

  proof
    wph
    cD
    cpnf
    wceq
    #
    vk
    cA
    cB
    cpr
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cD
    cE
    cxad
    co
    #
    wceq
    #
    wph
    @0
    wa
    #
    cpnf
    cpnf
    cE
    cxad
    co
    #
    @3
    @4
    wph
    cpnf
    @7
    wceq
    @0
    wph
    @7
    cpnf
    wph
    cE
    cxr
    wcel
    #
    cE
    cmnf
    wne
    @7
    cpnf
    wceq
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cE
    cc0
    cpnf
    iccssxr
    #
    sge0pr.e
    sseldi
    #
    wph
    cmnf
    cE
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    #
    @11
    wph
    cmnf
    cc0
    cE
    @12
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    @11
    cmnf
    cc0
    clt
    wbr
    wph
    mnflt0
    a1i
    #
    wph
    @13
    cpnf
    cxr
    wcel
    #
    cE
    @9
    wcel
    #
    cc0
    cE
    cle
    wbr
    #
    @14
    @16
    wph
    pnfxr
    a1i
    #
    sge0pr.e
    cc0
    cpnf
    cE
    iccgelb
    syl3anc
    #
    xrltletrd
    xrgtned
    cE
    xaddpnf2
    syl2anc
    eqcomd
    adantr
    @6
    @2
    cvv
    @1
    @1
    cvv
    wcel
    #
    @6
    cA
    cB
    prex
    #
    a1i
    wph
    @1
    @9
    @2
    wf
    #
    @0
    wph
    vk
    @1
    cC
    @9
    @2
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    @24
    cA
    wceq
    #
    cC
    @9
    wcel
    #
    wph
    @27
    @28
    @25
    wph
    @27
    wa
    cC
    cD
    @9
    @27
    cC
    cD
    wceq
    #
    wph
    sge0pr.cd
    adantl
    wph
    cD
    @9
    wcel
    #
    @27
    sge0pr.d
    adantr
    eqeltrd
    adantlr
    @26
    @27
    wn
    #
    wa
    wph
    @24
    cB
    wceq
    #
    @28
    wph
    @25
    @31
    simpll
    @25
    @31
    @32
    wph
    @25
    @31
    wa
    @25
    @24
    cA
    wne
    #
    @32
    @25
    @31
    simpl
    @31
    @33
    @25
    @24
    cA
    neqne
    adantl
    @24
    cA
    cB
    elprn1
    syl2anc
    #
    adantll
    wph
    @32
    wa
    cC
    cE
    @9
    @32
    cC
    cE
    wceq
    #
    wph
    sge0pr.ce
    adantl
    #
    wph
    @17
    @32
    sge0pr.e
    adantr
    eqeltrd
    syl2anc
    pm2.61dan
    @2
    eqid
    #
    fmptd
    #
    adantr
    @6
    cpnf
    cD
    @2
    crn
    #
    @0
    cpnf
    cD
    wceq
    wph
    @0
    cD
    cpnf
    @0
    id
    #
    eqcomd
    adantl
    wph
    cD
    @39
    wcel
    @0
    wph
    cD
    cD
    cE
    cpr
    #
    @39
    wph
    @30
    cD
    @41
    wcel
    sge0pr.d
    cD
    cE
    @9
    prid1g
    syl
    wph
    @39
    @41
    wph
    vk
    cA
    cB
    cC
    cD
    cE
    @2
    cV
    cW
    sge0pr.a
    sge0pr.b
    @37
    sge0pr.cd
    sge0pr.ce
    rnmptpr
    eqcomd
    #
    eleqtrd
    adantr
    eqeltrd
    sge0pnfval
    @0
    @4
    @7
    wceq
    wph
    cD
    cpnf
    cE
    cxad
    oveq1
    adantl
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    cE
    cpnf
    wceq
    #
    @5
    wph
    @45
    @5
    @43
    wph
    @45
    wa
    #
    cpnf
    cD
    cpnf
    cxad
    co
    #
    @3
    @4
    wph
    cpnf
    @47
    wceq
    @45
    wph
    @47
    cpnf
    wph
    cD
    cxr
    wcel
    #
    cD
    cmnf
    wne
    @47
    cpnf
    wceq
    wph
    @9
    cxr
    cD
    @10
    sge0pr.d
    sseldi
    #
    wph
    cmnf
    cD
    @12
    @49
    wph
    cmnf
    cc0
    cD
    @12
    @14
    @49
    @15
    wph
    @13
    @16
    @30
    cc0
    cD
    cle
    wbr
    #
    @14
    @19
    sge0pr.d
    cc0
    cpnf
    cD
    iccgelb
    syl3anc
    #
    xrltletrd
    xrgtned
    cD
    xaddpnf1
    syl2anc
    eqcomd
    adantr
    @46
    @2
    cvv
    @1
    @21
    @46
    @22
    a1i
    wph
    @23
    @45
    @38
    adantr
    @46
    cpnf
    cE
    @39
    @45
    cpnf
    cE
    wceq
    wph
    @45
    cE
    cpnf
    @45
    id
    #
    eqcomd
    adantl
    wph
    cE
    @39
    wcel
    @45
    wph
    cE
    @41
    @39
    wph
    @17
    cE
    @41
    wcel
    sge0pr.e
    cD
    cE
    @9
    prid2g
    syl
    @42
    eleqtrd
    adantr
    eqeltrd
    sge0pnfval
    @45
    @4
    @47
    wceq
    wph
    cE
    cpnf
    cD
    cxad
    oveq2
    adantl
    3eqtr4d
    adantlr
    @44
    @45
    wn
    #
    wa
    #
    @1
    cC
    vk
    csu
    cD
    cE
    caddc
    co
    #
    @3
    @4
    @54
    cA
    cB
    cC
    cD
    vk
    cE
    cV
    cW
    sge0pr.cd
    sge0pr.ce
    @54
    cD
    cc
    wcel
    cE
    cc
    wcel
    #
    @54
    cc0
    cpnf
    cico
    co
    #
    cc
    cD
    @57
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    @44
    cD
    @57
    wcel
    #
    @53
    @44
    cc0
    cpnf
    cD
    @13
    @44
    0xr
    a1i
    @16
    @44
    pnfxr
    a1i
    #
    wph
    @48
    @43
    @49
    adantr
    #
    wph
    @50
    @43
    @51
    adantr
    @44
    cD
    cpnf
    @61
    @60
    wph
    cD
    cpnf
    cle
    wbr
    #
    @43
    wph
    @48
    @62
    @49
    cD
    pnfge
    syl
    adantr
    @43
    cD
    cpnf
    wne
    wph
    @0
    cD
    cpnf
    @40
    necon3bi
    adantl
    xrleneltd
    elicod
    #
    adantr
    #
    sseldi
    wph
    @53
    @56
    @43
    wph
    @53
    wa
    #
    @57
    cc
    cE
    @58
    @65
    cc0
    cpnf
    cE
    @13
    @65
    0xr
    a1i
    @16
    @65
    pnfxr
    a1i
    #
    wph
    @8
    @53
    @11
    adantr
    #
    wph
    @18
    @53
    @20
    adantr
    @65
    cE
    cpnf
    @67
    @66
    wph
    cE
    cpnf
    cle
    wbr
    #
    @53
    wph
    @8
    @68
    @11
    cE
    pnfge
    syl
    adantr
    @53
    cE
    cpnf
    wne
    wph
    @45
    cE
    cpnf
    @52
    necon3bi
    adantl
    xrleneltd
    elicod
    #
    sseldi
    adantlr
    jca
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    @43
    @53
    wph
    @70
    @71
    sge0pr.a
    sge0pr.b
    jca
    ad2antrr
    wph
    cA
    cB
    wne
    @43
    @53
    sge0pr.ab
    ad2antrr
    sumpr
    @54
    @1
    cC
    vk
    @1
    cfn
    wcel
    @54
    cA
    cB
    prfi
    a1i
    @54
    @25
    wa
    #
    @27
    cC
    @57
    wcel
    #
    @44
    @27
    @73
    @53
    @25
    @44
    @27
    wa
    cC
    cD
    @57
    @27
    @29
    @44
    sge0pr.cd
    adantl
    @44
    @59
    @27
    @63
    adantr
    eqeltrd
    ad4ant14
    @72
    @31
    wa
    wph
    @53
    @32
    @73
    wph
    @43
    @53
    @25
    @31
    simp-4l
    @44
    @53
    @25
    @31
    simpllr
    @25
    @31
    @32
    @54
    @34
    adantll
    wph
    @53
    @32
    w3a
    cC
    cE
    @57
    wph
    @32
    @35
    @53
    @36
    3adant2
    wph
    @53
    cE
    @57
    wcel
    @32
    @69
    3adant3
    eqeltrd
    syl3anc
    pm2.61dan
    sge0fsummpt
    @54
    cD
    cr
    wcel
    cE
    cr
    wcel
    #
    @4
    @55
    wceq
    @54
    @57
    cr
    cD
    rge0ssre
    @64
    sseldi
    wph
    @53
    @74
    @43
    @65
    @57
    cr
    cE
    rge0ssre
    @69
    sseldi
    adantlr
    cD
    cE
    rexadd
    syl2anc
    3eqtr4d
    pm2.61dan
    pm2.61dan
end
