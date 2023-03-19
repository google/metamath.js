include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "sge0xrclmpt.mm"
include "cc0.mm"
include "cicc.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0nemnf.mm"
include "xaddpnf2.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cv.mm"
include "ge0xaddcl.mm"
include "cle.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wbr.mm"
include "cvv.mm"
include "elexd.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xadd0ge.mm"
include "sge0lempt.mm"
include "eqbrtrd.mm"
include "xrgepnfd.mm"
include "3eqtrrd.mm"
include "wn.mm"
include "cr.mm"
include "simpl.mm"
include "wb.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "sge0xrcl.mm"
include "xaddpnf1.mm"
include "xadd0ge2.mm"
include "adantlr.mm"
include "csb.mm"
include "ad2antrr.mm"
include "cico.mm"
include "wi.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfel.mm"
include "nfan.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "sge0rernmpt.mm"
include "chvar.mm"
include "adantllr.mm"
include "cbvmpt.mm"
include "fveq2i.mm"
include "simplr.mm"
include "syl5eqelr.mm"
include "sge0xaddlem2.mm"
include "nfov.mm"
include "oveq12d.mm"
include "oveq12i.mm"
include "eqeq12i.mm"
include "sylibr.mm"
include "pm2.61dan.mm"

theorem sge0xadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vj: setvar j
  let vx: setvar x
  assume sge0xadd.kph: |- F/ k ph
  assume sge0xadd.a: |- ( ph -> A e. V )
  assume sge0xadd.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0xadd.c: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> ( B +e C ) ) ) = ( ( sum^ ` ( k e. A |-> B ) ) +e ( sum^ ` ( k e. A |-> C ) ) ) )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    vk
    cA
    cB
    cC
    cxad
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    @1
    vk
    cA
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    wceq
    #
    wph
    @2
    wa
    #
    @8
    cpnf
    @7
    cxad
    co
    #
    cpnf
    @5
    @10
    @1
    cpnf
    @7
    cxad
    wph
    @2
    simpr
    oveq1d
    wph
    @11
    cpnf
    wceq
    #
    @2
    wph
    @7
    cxr
    wcel
    @7
    cmnf
    wne
    @12
    wph
    vk
    cA
    cC
    cV
    sge0xadd.kph
    sge0xadd.a
    sge0xadd.c
    sge0xrclmpt
    wph
    cA
    @6
    cV
    sge0xadd.a
    wph
    vk
    cA
    cC
    cc0
    cpnf
    cicc
    co
    #
    @6
    sge0xadd.kph
    sge0xadd.c
    @6
    eqid
    fmptdf
    #
    sge0nemnf
    @7
    xaddpnf2
    syl2anc
    adantr
    @10
    @5
    cpnf
    @10
    @5
    wph
    @5
    cxr
    wcel
    #
    @2
    wph
    vk
    cA
    @3
    cV
    sge0xadd.kph
    sge0xadd.a
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    @13
    wcel
    #
    cC
    @13
    wcel
    #
    @3
    @13
    wcel
    sge0xadd.b
    sge0xadd.c
    cB
    cC
    ge0xaddcl
    syl2anc
    #
    sge0xrclmpt
    #
    adantr
    @10
    cpnf
    @1
    @5
    cle
    @2
    cpnf
    @1
    wceq
    wph
    @2
    @1
    cpnf
    @2
    id
    eqcomd
    adantl
    wph
    @1
    @5
    cle
    wbr
    @2
    wph
    vk
    cA
    cB
    @3
    cvv
    sge0xadd.kph
    wph
    cA
    cV
    sge0xadd.a
    elexd
    sge0xadd.b
    @21
    @18
    cB
    cC
    @18
    @13
    cxr
    cB
    cc0
    cpnf
    iccssxr
    #
    sge0xadd.b
    sseldi
    sge0xadd.c
    xadd0ge
    sge0lempt
    adantr
    eqbrtrd
    xrgepnfd
    eqcomd
    3eqtrrd
    wph
    @2
    wn
    #
    wa
    #
    wph
    @1
    cr
    wcel
    #
    @9
    wph
    @24
    simpl
    @25
    @26
    @24
    wph
    @24
    simpr
    wph
    @26
    @24
    wb
    @24
    wph
    @0
    cV
    cA
    sge0xadd.a
    wph
    vk
    cA
    cB
    @13
    @0
    sge0xadd.kph
    sge0xadd.b
    @0
    eqid
    fmptdf
    #
    sge0repnf
    adantr
    mpbird
    wph
    @26
    wa
    #
    @7
    cpnf
    wceq
    #
    @9
    wph
    @29
    @9
    @26
    wph
    @29
    wa
    #
    @8
    @1
    cpnf
    cxad
    co
    #
    cpnf
    @5
    @30
    @7
    cpnf
    @1
    cxad
    wph
    @29
    simpr
    oveq2d
    wph
    @31
    cpnf
    wceq
    #
    @29
    wph
    @1
    cxr
    wcel
    @1
    cmnf
    wne
    @32
    wph
    @0
    cV
    cA
    sge0xadd.a
    @27
    sge0xrcl
    wph
    cA
    @0
    cV
    sge0xadd.a
    @27
    sge0nemnf
    @1
    xaddpnf1
    syl2anc
    adantr
    @30
    @5
    cpnf
    @30
    @5
    wph
    @15
    @29
    @22
    adantr
    @30
    cpnf
    @7
    @5
    cle
    @29
    cpnf
    @7
    wceq
    wph
    @29
    @7
    cpnf
    @29
    id
    eqcomd
    adantl
    wph
    @7
    @5
    cle
    wbr
    @29
    wph
    vk
    cA
    cC
    @3
    cV
    sge0xadd.kph
    sge0xadd.a
    sge0xadd.c
    @21
    @18
    cC
    cB
    @18
    @13
    cxr
    cC
    @23
    sge0xadd.c
    sseldi
    sge0xadd.b
    xadd0ge2
    sge0lempt
    adantr
    eqbrtrd
    xrgepnfd
    eqcomd
    3eqtrrd
    adantlr
    @28
    @29
    wn
    #
    wa
    @28
    @7
    cr
    wcel
    #
    @9
    @28
    @33
    simpl
    wph
    @33
    @34
    @26
    wph
    @33
    wa
    @34
    @33
    wph
    @33
    simpr
    wph
    @34
    @33
    wb
    @33
    wph
    @6
    cV
    cA
    sge0xadd.a
    @14
    sge0repnf
    adantr
    mpbird
    adantlr
    @28
    @34
    wa
    #
    vj
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vk
    @36
    cC
    csb
    #
    cxad
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    vj
    cA
    @37
    cmpt
    #
    csumge0
    cfv
    #
    vj
    cA
    @38
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    wceq
    @9
    @35
    cA
    @37
    @38
    vj
    cV
    wph
    cA
    cV
    wcel
    #
    @26
    @34
    sge0xadd.a
    ad2antrr
    @28
    @36
    cA
    wcel
    #
    @37
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @34
    @28
    @17
    wa
    #
    cB
    @49
    wcel
    #
    wi
    @28
    @48
    wa
    #
    @50
    wi
    vk
    vj
    @53
    @50
    vk
    @28
    @48
    vk
    wph
    @26
    vk
    sge0xadd.kph
    vk
    @1
    cr
    vk
    @0
    csumge0
    vk
    csumge0
    nfcv
    #
    vk
    cA
    cB
    nfmpt1
    nffv
    vk
    cr
    nfcv
    #
    nfel
    nfan
    #
    @48
    vk
    nfv
    #
    nfan
    vk
    @37
    @49
    vk
    @36
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @16
    @36
    wceq
    #
    @51
    @53
    @52
    @50
    @59
    @17
    @48
    @28
    @16
    @36
    cA
    eleq1
    #
    anbi2d
    @59
    cB
    @37
    @49
    vk
    @36
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    @28
    vk
    cA
    cB
    cV
    @56
    wph
    @47
    @26
    sge0xadd.a
    adantr
    wph
    @17
    @19
    @26
    sge0xadd.b
    adantlr
    wph
    @26
    simpr
    sge0rernmpt
    chvar
    adantlr
    wph
    @34
    @48
    @38
    @49
    wcel
    #
    @26
    wph
    @34
    wa
    #
    @17
    wa
    #
    cC
    @49
    wcel
    #
    wi
    @63
    @48
    wa
    #
    @62
    wi
    vk
    vj
    @66
    @62
    vk
    @63
    @48
    vk
    wph
    @34
    vk
    sge0xadd.kph
    vk
    @7
    cr
    vk
    @6
    csumge0
    @54
    vk
    cA
    cC
    nfmpt1
    nffv
    @55
    nfel
    nfan
    #
    @57
    nfan
    vk
    @38
    @49
    vk
    @36
    cC
    nfcsb1v
    #
    nfel1
    nfim
    @59
    @64
    @66
    @65
    @62
    @59
    @17
    @48
    @63
    @60
    anbi2d
    @59
    cC
    @38
    @49
    vk
    @36
    cC
    csbeq1a
    #
    eleq1d
    imbi12d
    @63
    vk
    cA
    cC
    cV
    @67
    wph
    @47
    @34
    sge0xadd.a
    adantr
    wph
    @17
    @20
    @34
    sge0xadd.c
    adantlr
    wph
    @34
    simpr
    sge0rernmpt
    chvar
    adantllr
    @35
    @43
    @1
    cr
    @0
    @42
    csumge0
    vk
    vj
    cA
    cB
    @37
    vj
    cB
    nfcv
    @58
    @61
    cbvmpt
    fveq2i
    #
    wph
    @26
    @34
    simplr
    syl5eqelr
    @35
    @45
    @7
    cr
    @6
    @44
    csumge0
    vk
    vj
    cA
    cC
    @38
    vj
    cC
    nfcv
    @68
    @69
    cbvmpt
    fveq2i
    #
    @28
    @34
    simpr
    syl5eqelr
    sge0xaddlem2
    @5
    @41
    @8
    @46
    @4
    @40
    csumge0
    vk
    vj
    cA
    @3
    @39
    vj
    @3
    nfcv
    vk
    @37
    @38
    cxad
    @58
    vk
    cxad
    nfcv
    @68
    nfov
    @59
    cB
    @37
    cC
    @38
    cxad
    @61
    @69
    oveq12d
    cbvmpt
    fveq2i
    @1
    @43
    @7
    @45
    cxad
    @70
    @71
    oveq12i
    eqeq12i
    sylibr
    syl2anc
    pm2.61dan
    syl2anc
    pm2.61dan
end
