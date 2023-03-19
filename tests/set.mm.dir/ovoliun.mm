include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wbr.mm"
include "cn.mm"
include "ciun.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wa.mm"
include "wb.mm"
include "wss.mm"
include "wf.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cv.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "serfre.mm"
include "feq1i.mm"
include "sylibr.mm"
include "frn.mm"
include "syl.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "xrrebnd.mm"
include "mnfxr.mm"
include "a1i.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "rexrd.mm"
include "mnflt.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "xrltletrd.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "co.mm"
include "crp.mm"
include "wral.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "fveq2i.mm"
include "cmpt.mm"
include "nffv.mm"
include "wceq.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nfss.mm"
include "sseq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "r19.21bi.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "simplr.mm"
include "simpr.mm"
include "ovoliunlem3.mm"
include "syl5eqbr.mm"
include "iunss.mm"
include "ovolcl.mm"
include "xralrple.mm"
include "sylan.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbird.mm"
include "wn.mm"
include "nltpnft.mm"
include "pnfge.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "pm2.61d.mm"

theorem ovoliun
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
  assert |- ( ph -> ( vol* ` U_ n e. NN A ) <_ sup ( ran T , RR* , < ) )

  proof
    wph
    cT
    crn
    #
    cxr
    clt
    csup
    #
    cpnf
    clt
    wbr
    #
    vn
    cn
    cA
    ciun
    #
    covol
    cfv
    #
    @1
    cle
    wbr
    #
    wph
    @2
    @1
    cr
    wcel
    #
    @5
    wph
    @6
    cmnf
    @1
    clt
    wbr
    #
    @2
    wa
    #
    @2
    wph
    @1
    cxr
    wcel
    #
    @6
    @8
    wb
    wph
    @0
    cxr
    wss
    #
    @9
    wph
    @0
    cr
    cxr
    wph
    cn
    cr
    cT
    wf
    #
    @0
    cr
    wss
    wph
    cn
    cr
    caddc
    cG
    c1
    cseq
    #
    wf
    @11
    wph
    vk
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    cn
    cr
    vk
    cv
    cG
    wph
    vn
    cn
    cA
    covol
    cfv
    #
    cr
    cG
    ovoliun.v
    ovoliun.g
    fmptd
    ffvelrnda
    serfre
    cn
    cr
    cT
    @12
    ovoliun.t
    feq1i
    sylibr
    #
    cn
    cr
    cT
    frn
    syl
    ressxr
    syl6ss
    #
    @0
    supxrcl
    syl
    #
    @1
    xrrebnd
    syl
    wph
    @7
    @2
    wph
    cmnf
    c1
    cT
    cfv
    #
    @1
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    wph
    @17
    wph
    @11
    c1
    cn
    wcel
    #
    @17
    cr
    wcel
    #
    @14
    1nn
    cn
    cr
    c1
    cT
    ffvelrn
    sylancl
    #
    rexrd
    @16
    wph
    @19
    cmnf
    @17
    clt
    wbr
    @20
    @17
    mnflt
    syl
    wph
    @10
    @17
    @0
    wcel
    #
    @17
    @1
    cle
    wbr
    @15
    wph
    cT
    cn
    wfn
    #
    @18
    @21
    wph
    @11
    @22
    @14
    cn
    cr
    cT
    ffn
    syl
    1nn
    cn
    c1
    cT
    fnfvelrn
    sylancl
    @0
    @17
    supxrub
    syl2anc
    xrltletrd
    biantrurd
    bitr4d
    wph
    @6
    @5
    wph
    @6
    wa
    #
    @5
    @4
    @1
    vx
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @23
    @26
    vx
    crp
    @23
    @24
    crp
    wcel
    #
    wa
    #
    @4
    vm
    cn
    vn
    vm
    cv
    #
    cA
    csb
    #
    ciun
    #
    covol
    cfv
    @25
    cle
    @3
    @32
    covol
    vn
    vm
    cn
    cA
    @31
    vm
    cA
    nfcv
    vn
    @30
    cA
    nfcsb1v
    #
    vn
    @30
    cA
    csbeq1a
    #
    cbviun
    fveq2i
    @29
    @31
    @24
    cT
    vm
    cG
    ovoliun.t
    cG
    vn
    cn
    @13
    cmpt
    vm
    cn
    @31
    covol
    cfv
    #
    cmpt
    ovoliun.g
    vn
    vm
    cn
    @13
    @35
    vm
    @13
    nfcv
    #
    vn
    @31
    covol
    vn
    covol
    nfcv
    @33
    nffv
    #
    vn
    cv
    @30
    wceq
    #
    cA
    @31
    covol
    @34
    fveq2d
    #
    cbvmpt
    eqtri
    @29
    @31
    cr
    wss
    #
    vm
    cn
    wph
    @40
    vm
    cn
    wral
    #
    @6
    @28
    wph
    cA
    cr
    wss
    #
    vn
    cn
    wral
    #
    @41
    wph
    @42
    vn
    cn
    ovoliun.a
    ralrimiva
    #
    @42
    @40
    vn
    vm
    cn
    @42
    vm
    nfv
    vn
    @31
    cr
    @33
    vn
    cr
    nfcv
    nfss
    @38
    cA
    @31
    cr
    @34
    sseq1d
    cbvral
    sylib
    ad2antrr
    r19.21bi
    @29
    @35
    cr
    wcel
    #
    vm
    cn
    wph
    @45
    vm
    cn
    wral
    #
    @6
    @28
    wph
    @13
    cr
    wcel
    #
    vn
    cn
    wral
    @46
    wph
    @47
    vn
    cn
    ovoliun.v
    ralrimiva
    @47
    @45
    vn
    vm
    cn
    vm
    @13
    cr
    @36
    nfel1
    vn
    @35
    cr
    @37
    nfel1
    @38
    @13
    @35
    cr
    @39
    eleq1d
    cbvral
    sylib
    ad2antrr
    r19.21bi
    wph
    @6
    @28
    simplr
    @23
    @28
    simpr
    ovoliunlem3
    syl5eqbr
    ralrimiva
    wph
    @4
    cxr
    wcel
    #
    @6
    @5
    @27
    wb
    wph
    @3
    cr
    wss
    #
    @48
    wph
    @43
    @49
    @44
    vn
    cn
    cA
    cr
    iunss
    sylibr
    @3
    ovolcl
    syl
    #
    vx
    @4
    @1
    xralrple
    sylan
    mpbird
    ex
    sylbird
    wph
    @2
    wn
    #
    @1
    cpnf
    wceq
    #
    @5
    wph
    @9
    @52
    @51
    wb
    @16
    @1
    nltpnft
    syl
    wph
    @5
    @52
    @4
    cpnf
    cle
    wbr
    #
    wph
    @48
    @53
    @50
    @4
    pnfge
    syl
    @1
    cpnf
    @4
    cle
    breq2
    syl5ibrcom
    sylbird
    pm2.61d
end
