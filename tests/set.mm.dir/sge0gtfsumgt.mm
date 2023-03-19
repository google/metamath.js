include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "csu.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfel.mm"
include "nfan.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cico.mm"
include "icossicc.mm"
include "sseldi.mm"
include "adantlr.mm"
include "crp.mm"
include "wb.mm"
include "simpr.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "sge0ltfirpmpt2.mm"
include "cc.mm"
include "nfv.mm"
include "elinel2.mm"
include "adantl.mm"
include "simpll.mm"
include "wss.mm"
include "elpwinss.mm"
include "sseldd.mm"
include "adantll.mm"
include "rge0ssre.mm"
include "fsumreclf.mm"
include "recnd.mm"
include "ad4ant13.mm"
include "ad2antrr.mm"
include "subcld.mm"
include "addcomd.mm"
include "breqtrd.mm"
include "resubcld.mm"
include "ltsubadd2d.mm"
include "mpbird.mm"
include "nncand.mm"
include "breq1d.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "wn.mm"
include "wceq.mm"
include "simpl.mm"
include "eqid.mm"
include "fmptdf.mm"
include "a1i.mm"
include "fssd.mm"
include "sge0repnf.mm"
include "mtbid.mm"
include "notnotb.mm"
include "sylibr.mm"
include "nfeq1.mm"
include "sge0pnffsumgt.mm"
include "pm2.61dan.mm"

theorem sge0gtfsumgt
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0gtfsumgt.k: |- F/ k ph
  assume sge0gtfsumgt.a: |- ( ph -> A e. V )
  assume sge0gtfsumgt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )
  assume sge0gtfsumgt.c: |- ( ph -> C e. RR )
  assume sge0gtfsumgt.l: |- ( ph -> C < ( sum^ ` ( k e. A |-> B ) ) )

  disjoint A k
  disjoint A y
  disjoint k y
  disjoint B y
  disjoint C y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. y e. ( ~P A i^i Fin ) C < sum_ k e. y B )

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
    cr
    wcel
    #
    cC
    vy
    cv
    #
    cB
    vk
    csu
    #
    clt
    wbr
    #
    vy
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    @2
    wa
    #
    @1
    @4
    @1
    cC
    cmin
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vy
    @7
    wrex
    @8
    @9
    vk
    vy
    cA
    cB
    cV
    @10
    wph
    @2
    vk
    sge0gtfsumgt.k
    vk
    @1
    cr
    vk
    @0
    csumge0
    vk
    csumge0
    nfcv
    vk
    cA
    cB
    nfmpt1
    nffv
    #
    vk
    cr
    nfcv
    nfel
    nfan
    wph
    cA
    cV
    wcel
    #
    @2
    sge0gtfsumgt.a
    adantr
    wph
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @2
    wph
    @16
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    @17
    cB
    cc0
    cpnf
    icossicc
    #
    sge0gtfsumgt.b
    sseldi
    adantlr
    @9
    cC
    @1
    clt
    wbr
    #
    @10
    crp
    wcel
    #
    wph
    @21
    @2
    sge0gtfsumgt.l
    adantr
    @9
    cC
    cr
    wcel
    #
    @2
    @21
    @22
    wb
    wph
    @23
    @2
    sge0gtfsumgt.c
    adantr
    #
    wph
    @2
    simpr
    #
    cC
    @1
    difrp
    syl2anc
    mpbid
    @25
    sge0ltfirpmpt2
    @9
    @12
    @5
    vy
    @7
    @9
    @3
    @7
    wcel
    #
    wa
    #
    @12
    @5
    @27
    @12
    wa
    #
    @1
    @10
    cmin
    co
    #
    @4
    clt
    wbr
    #
    @5
    @28
    @30
    @1
    @10
    @4
    caddc
    co
    #
    clt
    wbr
    @28
    @1
    @11
    @31
    clt
    @27
    @12
    simpr
    @28
    @4
    @10
    wph
    @26
    @4
    cc
    wcel
    @2
    @12
    wph
    @26
    wa
    #
    @4
    @32
    @3
    cB
    vk
    wph
    @26
    vk
    sge0gtfsumgt.k
    @26
    vk
    nfv
    nfan
    @26
    @3
    cfn
    wcel
    wph
    @3
    @6
    cfn
    elinel2
    adantl
    @32
    @15
    @3
    wcel
    #
    wa
    wph
    @16
    cB
    cr
    wcel
    wph
    @26
    @33
    simpll
    @26
    @33
    @16
    wph
    @26
    @33
    wa
    @3
    cA
    @15
    @26
    @3
    cA
    wss
    @33
    @3
    cA
    cfn
    elpwinss
    adantr
    @26
    @33
    simpr
    sseldd
    adantll
    @18
    @19
    cr
    cB
    rge0ssre
    sge0gtfsumgt.b
    sseldi
    syl2anc
    fsumreclf
    #
    recnd
    ad4ant13
    @28
    @1
    cC
    @28
    @1
    @9
    @2
    @26
    @12
    @25
    ad2antrr
    #
    recnd
    #
    @28
    cC
    @9
    @23
    @26
    @12
    @24
    ad2antrr
    #
    recnd
    #
    subcld
    addcomd
    breqtrd
    @28
    @1
    @10
    @4
    @35
    @28
    @1
    cC
    @35
    @37
    resubcld
    wph
    @26
    @4
    cr
    wcel
    @2
    @12
    @34
    ad4ant13
    ltsubadd2d
    mpbird
    @28
    @29
    cC
    @4
    clt
    @28
    @1
    cC
    @36
    @38
    nncand
    breq1d
    mpbid
    ex
    reximdva
    mpd
    wph
    @2
    wn
    #
    wa
    #
    wph
    @1
    cpnf
    wceq
    #
    @8
    wph
    @39
    simpl
    @40
    @41
    wn
    #
    wn
    @41
    @40
    @2
    @42
    wph
    @39
    simpr
    wph
    @2
    @42
    wb
    @39
    wph
    @0
    cV
    cA
    sge0gtfsumgt.a
    wph
    cA
    @19
    @17
    @0
    wph
    vk
    cA
    cB
    @19
    @0
    sge0gtfsumgt.k
    sge0gtfsumgt.b
    @0
    eqid
    fmptdf
    @19
    @17
    wss
    wph
    @20
    a1i
    fssd
    sge0repnf
    adantr
    mtbid
    @41
    notnotb
    sylibr
    wph
    @41
    wa
    vy
    cA
    cB
    vk
    cV
    cC
    wph
    @41
    vk
    sge0gtfsumgt.k
    vk
    @1
    cpnf
    @13
    nfeq1
    nfan
    wph
    @14
    @41
    sge0gtfsumgt.a
    adantr
    wph
    @16
    cB
    @19
    wcel
    @41
    sge0gtfsumgt.b
    adantlr
    wph
    @41
    simpr
    wph
    @23
    @41
    sge0gtfsumgt.c
    adantr
    sge0pnffsumgt
    syl2anc
    pm2.61dan
end
