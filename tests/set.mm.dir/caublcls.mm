include "c1st.mm"
include "ccom.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cbl.mm"
include "cuz.mm"
include "eqid.mm"
include "cxmt.mm"
include "ctopon.mm"
include "3ad2ant1.mm"
include "mopntopon.mm"
include "syl.mm"
include "simp3.mm"
include "nnzd.mm"
include "simp2.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "wral.mm"
include "eluznn.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "anassrs.mm"
include "sstr2.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "3adantl2.mm"
include "c2nd.mm"
include "crp.mm"
include "adantr.mm"
include "cxp.mm"
include "wf.mm"
include "simpl1.mm"
include "3ad2antl3.mm"
include "ffvelrnd.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "cop.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "3eltr4d.mm"
include "sseldd.mm"
include "ffvelrnda.mm"
include "3adant2.mm"
include "cxr.mm"
include "rpxrd.mm"
include "blssm.mm"
include "eqsstrd.mm"
include "lmcls.mm"

theorem caublcls
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vr: setvar r
  assume caubl.2: |- ( ph -> D e. ( *Met ` X ) )
  assume caubl.3: |- ( ph -> F : NN --> ( X X. RR+ ) )
  assume caubl.4: |- ( ph -> A. n e. NN ( ( ball ` D ) ` ( F ` ( n + 1 ) ) ) C_ ( ( ball ` D ) ` ( F ` n ) ) )
  assume caublcls.6: |- J = ( MetOpen ` D )

  disjoint D n
  disjoint F n
  disjoint X n
  disjoint k r
  disjoint A k
  disjoint A r
  disjoint k n
  disjoint D k
  disjoint n r
  disjoint D r
  disjoint F k
  disjoint F r
  disjoint k ph
  disjoint ph r
  disjoint X k
  disjoint X r
  disjoint J k
  disjoint P k
  assert |- ( ( ph /\ ( 1st o. F ) ( ~~>t ` J ) P /\ A e. NN ) -> P e. ( ( cls ` J ) ` ( ( ball ` D ) ` ( F ` A ) ) ) )

  proof
    wph
    c1st
    cF
    ccom
    #
    cP
    cJ
    clm
    cfv
    wbr
    #
    cA
    cn
    wcel
    #
    w3a
    #
    cP
    cA
    cF
    cfv
    #
    cD
    cbl
    cfv
    #
    cfv
    #
    vk
    @0
    cJ
    cA
    cX
    cA
    cuz
    cfv
    #
    @7
    eqid
    @3
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    wph
    @1
    @8
    @2
    caubl.2
    3ad2ant1
    #
    cD
    cJ
    cX
    caublcls.6
    mopntopon
    syl
    @3
    cA
    wph
    @1
    @2
    simp3
    nnzd
    wph
    @1
    @2
    simp2
    @3
    vk
    cv
    #
    @7
    wcel
    #
    wa
    #
    @10
    cF
    cfv
    #
    @5
    cfv
    #
    @6
    @10
    @0
    cfv
    #
    wph
    @2
    @11
    @14
    @6
    wss
    #
    @1
    @11
    wph
    @2
    wa
    #
    @16
    @17
    vr
    cv
    #
    cF
    cfv
    #
    @5
    cfv
    #
    @6
    wss
    #
    wi
    @17
    @6
    @6
    wss
    #
    wi
    @17
    @16
    wi
    #
    @17
    @10
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @5
    cfv
    #
    @6
    wss
    #
    wi
    @23
    vr
    vk
    cA
    @10
    @18
    cA
    wceq
    #
    @21
    @22
    @17
    @28
    @20
    @6
    @6
    @28
    @19
    @4
    @5
    @18
    cA
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    @18
    @10
    wceq
    #
    @21
    @16
    @17
    @29
    @20
    @14
    @6
    @29
    @19
    @13
    @5
    @18
    @10
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    #
    @18
    @24
    wceq
    #
    @21
    @27
    @17
    @31
    @20
    @26
    @6
    @31
    @19
    @25
    @5
    @18
    @24
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    @30
    @22
    cA
    cz
    wcel
    @17
    @6
    ssid
    2a1i
    @11
    @17
    @16
    @27
    @17
    @11
    @16
    @27
    wi
    #
    @17
    @11
    wa
    @26
    @14
    wss
    #
    @32
    wph
    @2
    @11
    @33
    wph
    vn
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @5
    cfv
    #
    @34
    cF
    cfv
    #
    @5
    cfv
    #
    wss
    #
    vn
    cn
    wral
    @10
    cn
    wcel
    #
    @33
    @2
    @11
    wa
    caubl.4
    @10
    cA
    eluznn
    #
    @40
    @33
    vn
    @10
    cn
    @34
    @10
    wceq
    #
    @37
    @26
    @39
    @14
    @43
    @36
    @25
    @5
    @43
    @35
    @24
    cF
    @34
    @10
    c1
    caddc
    oveq1
    fveq2d
    fveq2d
    @43
    @38
    @13
    @5
    @34
    @10
    cF
    fveq2
    fveq2d
    sseq12d
    rspccva
    syl2an
    anassrs
    @26
    @14
    @6
    sstr2
    syl
    expcom
    a2d
    uzind4
    impcom
    3adantl2
    @12
    @13
    c1st
    cfv
    #
    @44
    @13
    c2nd
    cfv
    #
    @5
    co
    #
    @15
    @14
    @12
    @8
    @44
    cX
    wcel
    #
    @45
    crp
    wcel
    #
    @44
    @46
    wcel
    @3
    @8
    @11
    @9
    adantr
    @12
    @13
    cX
    crp
    cxp
    #
    wcel
    #
    @47
    @12
    cn
    @49
    @10
    cF
    @12
    wph
    cn
    @49
    cF
    wf
    #
    wph
    @1
    @2
    @11
    simpl1
    caubl.3
    syl
    #
    @2
    wph
    @11
    @41
    @1
    @42
    3ad2antl3
    #
    ffvelrnd
    #
    @13
    cX
    crp
    xp1st
    syl
    @12
    @50
    @48
    @54
    @13
    cX
    crp
    xp2nd
    syl
    cD
    @44
    @45
    cX
    blcntr
    syl3anc
    @12
    @51
    @41
    @15
    @44
    wceq
    @52
    @53
    cn
    @49
    @10
    c1st
    cF
    fvco3
    syl2anc
    @12
    @14
    @44
    @45
    cop
    #
    @5
    cfv
    @46
    @12
    @13
    @55
    @5
    @12
    @50
    @13
    @55
    wceq
    @54
    @13
    cX
    crp
    1st2nd2
    syl
    fveq2d
    @44
    @45
    @5
    df-ov
    syl6eqr
    3eltr4d
    sseldd
    @3
    @6
    @4
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    @5
    co
    #
    cX
    @3
    @6
    @56
    @57
    cop
    #
    @5
    cfv
    @58
    @3
    @4
    @59
    @5
    @3
    @4
    @49
    wcel
    #
    @4
    @59
    wceq
    wph
    @2
    @60
    @1
    wph
    cn
    @49
    cA
    cF
    caubl.3
    ffvelrnda
    3adant2
    #
    @4
    cX
    crp
    1st2nd2
    syl
    fveq2d
    @56
    @57
    @5
    df-ov
    syl6eqr
    @3
    @8
    @56
    cX
    wcel
    #
    @57
    cxr
    wcel
    @58
    cX
    wss
    @9
    @3
    @60
    @62
    @61
    @4
    cX
    crp
    xp1st
    syl
    @3
    @57
    @3
    @60
    @57
    crp
    wcel
    @61
    @4
    cX
    crp
    xp2nd
    syl
    rpxrd
    cD
    @56
    @57
    cX
    blssm
    syl3anc
    eqsstrd
    lmcls
end
