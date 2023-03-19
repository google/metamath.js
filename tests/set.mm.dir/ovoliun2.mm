include "cn.mm"
include "ciun.mm"
include "covol.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csu.mm"
include "cle.mm"
include "ovoliun.mm"
include "cv.mm"
include "csb.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "wf.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "fvex.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "csbeq1a.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "feq1i.mm"
include "sylibr.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "1nn.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "cli.mm"
include "syl5eqelr.mm"
include "isumrecl.mm"
include "cfz.mm"
include "co.mm"
include "elfznn.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "simpl.mm"
include "syl2an.mm"
include "recnd.mm"
include "fsumser.mm"
include "fveq1i.mm"
include "syl6eqr.mm"
include "fzfid.mm"
include "ssriv.mm"
include "a1i.mm"
include "cc0.mm"
include "nfv.mm"
include "nfss.mm"
include "sseq1d.mm"
include "ovolge0.mm"
include "isumless.mm"
include "adantr.mm"
include "eqbrtrrd.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "supxrre.mm"
include "syl3anc.mm"
include "isumsup.mm"
include "eqtr4d.mm"
include "cbvsumi.mm"
include "breqtrd.mm"

theorem ovoliun2
  let wph: wff ph
  let cA: class A
  let cT: class T
  let vn: setvar n
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let cF: class F
  let vw: setvar w
  let cJ: class J
  let cK: class K
  let cL: class L
  let cH: class H
  let cS: class S
  let cU: class U
  assume ovoliun.t: |- T = seq 1 ( + , G )
  assume ovoliun.g: |- G = ( n e. NN |-> ( vol* ` A ) )
  assume ovoliun.a: |- ( ( ph /\ n e. NN ) -> A C_ RR )
  assume ovoliun.v: |- ( ( ph /\ n e. NN ) -> ( vol* ` A ) e. RR )
  assume ovoliun2.t: |- ( ph -> T e. dom ~~> )

  disjoint n ph
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f n
  disjoint B f
  disjoint g n
  disjoint B g
  disjoint j n
  disjoint B j
  disjoint k n
  disjoint B k
  disjoint m n
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint f i
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F z
  disjoint i w
  disjoint i y
  disjoint J i
  disjoint j w
  disjoint J j
  disjoint k w
  disjoint J k
  disjoint m w
  disjoint J m
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K n
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint H f
  disjoint H j
  disjoint H m
  disjoint H n
  disjoint H z
  disjoint g i
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G k
  disjoint G m
  disjoint G x
  disjoint T g
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U f
  disjoint U j
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( vol* ` U_ n e. NN A ) <_ sum_ n e. NN ( vol* ` A ) )

  proof
    wph
    vn
    cn
    cA
    ciun
    covol
    cfv
    cT
    crn
    #
    cxr
    clt
    csup
    #
    cn
    cA
    covol
    cfv
    #
    vn
    csu
    #
    cle
    wph
    cA
    cT
    vn
    cG
    ovoliun.t
    ovoliun.g
    ovoliun.a
    ovoliun.v
    ovoliun
    wph
    @1
    cn
    vn
    vm
    cv
    #
    cA
    csb
    #
    covol
    cfv
    #
    vm
    csu
    #
    @3
    wph
    @1
    @0
    cr
    clt
    csup
    #
    @7
    wph
    @0
    cr
    wss
    #
    @0
    c0
    wne
    #
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    @0
    wral
    #
    vx
    cr
    wrex
    #
    @1
    @8
    wceq
    wph
    cn
    cr
    cT
    wf
    #
    @9
    wph
    cn
    cr
    caddc
    cG
    c1
    cseq
    #
    wf
    @16
    wph
    vm
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    #
    wph
    @4
    cn
    wcel
    #
    wa
    #
    @4
    cG
    cfv
    #
    @6
    cr
    @19
    @21
    @6
    wceq
    #
    wph
    @19
    @6
    cvv
    wcel
    @22
    @5
    covol
    fvex
    vm
    cn
    @6
    cvv
    cG
    cG
    vn
    cn
    @2
    cmpt
    vm
    cn
    @6
    cmpt
    ovoliun.g
    vn
    vm
    cn
    @2
    @6
    vm
    @2
    nfcv
    #
    vn
    @5
    covol
    vn
    covol
    nfcv
    vn
    @4
    cA
    nfcsb1v
    #
    nffv
    #
    vn
    cv
    #
    @4
    wceq
    #
    cA
    @5
    covol
    vn
    @4
    cA
    csbeq1a
    #
    fveq2d
    #
    cbvmpt
    eqtri
    fvmpt2
    mpan2
    #
    adantl
    #
    wph
    @6
    cr
    wcel
    #
    vm
    cn
    wph
    @2
    cr
    wcel
    #
    vn
    cn
    wral
    @32
    vm
    cn
    wral
    wph
    @33
    vn
    cn
    ovoliun.v
    ralrimiva
    @33
    @32
    vn
    vm
    cn
    vm
    @2
    cr
    @23
    nfel1
    vn
    @6
    cr
    @25
    nfel1
    @27
    @2
    @6
    cr
    @29
    eleq1d
    cbvral
    sylib
    r19.21bi
    #
    eqeltrd
    serfre
    cn
    cr
    cT
    @17
    ovoliun.t
    feq1i
    sylibr
    #
    cn
    cr
    cT
    frn
    syl
    wph
    cT
    cdm
    #
    c0
    wne
    #
    @10
    wph
    c1
    @36
    wcel
    @37
    wph
    c1
    cn
    @36
    1nn
    wph
    @16
    @36
    cn
    wceq
    @35
    cn
    cr
    cT
    fdm
    syl
    syl5eleqr
    @36
    c1
    ne0i
    syl
    @36
    c0
    @0
    c0
    cT
    dm0rn0
    necon3bii
    sylib
    wph
    @15
    vk
    cv
    #
    cT
    cfv
    #
    @12
    cle
    wbr
    #
    vk
    cn
    wral
    #
    vx
    cr
    wrex
    #
    wph
    @7
    cr
    wcel
    @39
    @7
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @42
    wph
    @6
    vm
    cG
    c1
    cn
    nnuz
    @18
    @31
    @34
    wph
    @17
    cT
    cli
    cdm
    ovoliun.t
    ovoliun2.t
    syl5eqelr
    #
    isumrecl
    wph
    @43
    vk
    cn
    wph
    @38
    cn
    wcel
    #
    wa
    #
    c1
    @38
    cfz
    co
    #
    @6
    vm
    csu
    #
    @39
    @7
    cle
    @47
    @49
    @38
    @17
    cfv
    @39
    @47
    @6
    vm
    cG
    c1
    @38
    @47
    @4
    @48
    wcel
    #
    wa
    #
    @19
    @22
    @50
    @19
    @47
    @4
    @38
    elfznn
    #
    adantl
    @30
    syl
    @47
    @38
    cn
    c1
    cuz
    cfv
    wph
    @46
    simpr
    nnuz
    syl6eleq
    @51
    @6
    @47
    wph
    @19
    @32
    @50
    wph
    @46
    simpl
    @52
    @34
    syl2an
    recnd
    fsumser
    @38
    cT
    @17
    ovoliun.t
    fveq1i
    syl6eqr
    wph
    @49
    @7
    cle
    wbr
    @46
    wph
    @48
    @6
    vm
    cG
    c1
    cn
    nnuz
    @18
    wph
    c1
    @38
    fzfid
    @48
    cn
    wss
    wph
    vn
    @48
    cn
    @26
    @38
    elfznn
    ssriv
    a1i
    @31
    @34
    @20
    @5
    cr
    wss
    #
    cc0
    @6
    cle
    wbr
    wph
    @53
    vm
    cn
    wph
    cA
    cr
    wss
    #
    vn
    cn
    wral
    @53
    vm
    cn
    wral
    wph
    @54
    vn
    cn
    ovoliun.a
    ralrimiva
    @54
    @53
    vn
    vm
    cn
    @54
    vm
    nfv
    vn
    @5
    cr
    @24
    vn
    cr
    nfcv
    nfss
    @27
    cA
    @5
    cr
    @28
    sseq1d
    cbvral
    sylib
    r19.21bi
    @5
    ovolge0
    syl
    #
    @45
    isumless
    adantr
    eqbrtrrd
    ralrimiva
    @41
    @44
    vx
    @7
    cr
    @12
    @7
    wceq
    @40
    @43
    vk
    cn
    @12
    @7
    @39
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    wph
    @14
    @41
    vx
    cr
    wph
    cT
    cn
    wfn
    #
    @14
    @41
    wb
    wph
    @16
    @57
    @35
    cn
    cr
    cT
    ffn
    syl
    @13
    @40
    vz
    vk
    cn
    cT
    @11
    @39
    @12
    cle
    breq1
    ralrn
    syl
    rexbidv
    mpbird
    vx
    vz
    @0
    supxrre
    syl3anc
    wph
    vx
    @6
    vk
    vm
    cG
    cT
    c1
    cn
    nnuz
    ovoliun.t
    @18
    @31
    @34
    @55
    @56
    isumsup
    eqtr4d
    cn
    @2
    @6
    vn
    vm
    @23
    @25
    @29
    cbvsumi
    syl6eqr
    breqtrd
end
