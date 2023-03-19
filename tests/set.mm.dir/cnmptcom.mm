include "cmpt2.mm"
include "cv.mm"
include "co.mm"
include "ctx.mm"
include "ccn.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "cuni.mm"
include "wf.mm"
include "wcel.mm"
include "wral.mm"
include "ctopon.mm"
include "cfv.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "ralcom.mm"
include "bitr3i.mm"
include "ffn.mm"
include "fnov.mm"
include "wa.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfmpt22.mm"
include "nfov.mm"
include "nfmpt21.mm"
include "nfeq.mm"
include "nfim.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "rsp2.mm"
include "syl11.mm"
include "w3a.mm"
include "ovmpt4g.mm"
include "3com12.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "syld.mm"
include "vtocl2gaf.mm"
include "com12.mm"
include "3impib.mm"
include "mpt2eq3dva.mm"
include "cnmpt2nd.mm"
include "cnmpt1st.mm"
include "cnmpt22f.mm"
include "eqeltrd.mm"

theorem cnmptcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume cnmptcom.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptcom.4: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptcom.6: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )

  disjoint x y
  disjoint L x
  disjoint L y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint Y y
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint J w
  disjoint J z
  disjoint K w
  disjoint K z
  disjoint w x
  disjoint w y
  disjoint L w
  disjoint x z
  disjoint y z
  disjoint L z
  disjoint X w
  disjoint X z
  disjoint ph w
  disjoint ph z
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> ( y e. Y , x e. X |-> A ) e. ( ( K tX J ) Cn L ) )

  proof
    wph
    vy
    vx
    cY
    cX
    cA
    cmpt2
    #
    vz
    vw
    cY
    cX
    vw
    cv
    #
    vz
    cv
    #
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    co
    #
    cmpt2
    #
    cK
    cJ
    ctx
    co
    cL
    ccn
    co
    wph
    @0
    vz
    vw
    cY
    cX
    @2
    @1
    @0
    co
    #
    cmpt2
    #
    @5
    wph
    @0
    cY
    cX
    cxp
    #
    wfn
    #
    @0
    @7
    wceq
    wph
    @8
    cL
    cuni
    #
    @0
    wf
    #
    @9
    wph
    cA
    @10
    wcel
    #
    vx
    cX
    wral
    vy
    cY
    wral
    #
    @11
    wph
    cX
    cY
    cxp
    #
    @10
    @3
    wf
    #
    @13
    wph
    cJ
    cK
    ctx
    co
    #
    @14
    ctopon
    cfv
    wcel
    #
    cL
    @10
    ctopon
    cfv
    wcel
    #
    @3
    @16
    cL
    ccn
    co
    wcel
    #
    @15
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @17
    cnmptcom.3
    cnmptcom.4
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    wph
    cL
    ctop
    wcel
    #
    @18
    wph
    @19
    @20
    cnmptcom.6
    @3
    @16
    cL
    cntop2
    syl
    cL
    @10
    @10
    eqid
    toptopon
    sylib
    cnmptcom.6
    @3
    @16
    cL
    @14
    @10
    cnf2
    syl3anc
    @15
    @12
    vy
    cY
    wral
    vx
    cX
    wral
    @13
    vx
    vy
    cX
    cY
    cA
    @10
    @3
    @3
    eqid
    #
    fmpt2
    @12
    vx
    vy
    cX
    cY
    ralcom
    bitr3i
    sylib
    #
    vy
    vx
    cY
    cX
    cA
    @10
    @0
    @0
    eqid
    #
    fmpt2
    sylib
    @8
    @10
    @0
    ffn
    syl
    vz
    vw
    cY
    cX
    @0
    fnov
    sylib
    wph
    vz
    vw
    cY
    cX
    @4
    @6
    wph
    @2
    cY
    wcel
    #
    @1
    cX
    wcel
    #
    @4
    @6
    wceq
    #
    @24
    @25
    wa
    wph
    @26
    wph
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    @28
    @27
    @0
    co
    #
    wceq
    #
    wi
    wph
    @27
    @2
    @3
    co
    #
    @2
    @27
    @0
    co
    #
    wceq
    #
    wi
    wph
    @26
    wi
    vy
    vx
    @2
    @1
    cY
    cX
    vy
    @2
    nfcv
    #
    vx
    @2
    nfcv
    #
    vx
    @1
    nfcv
    #
    wph
    @34
    vy
    wph
    vy
    nfv
    vy
    @32
    @33
    vy
    @27
    @2
    @3
    vy
    @27
    nfcv
    #
    vx
    vy
    cX
    cY
    cA
    nfmpt22
    @35
    nfov
    vy
    @2
    @27
    @0
    @35
    vy
    vx
    cY
    cX
    cA
    nfmpt21
    @38
    nfov
    nfeq
    nfim
    wph
    @26
    vx
    wph
    vx
    nfv
    vx
    @4
    @6
    vx
    @1
    @2
    @3
    @37
    vx
    vy
    cX
    cY
    cA
    nfmpt21
    @36
    nfov
    vx
    @2
    @1
    @0
    @36
    vy
    vx
    cY
    cX
    cA
    nfmpt22
    @37
    nfov
    nfeq
    nfim
    @28
    @2
    wceq
    #
    @31
    @34
    wph
    @39
    @29
    @32
    @30
    @33
    @28
    @2
    @27
    @3
    oveq2
    @28
    @2
    @27
    @0
    oveq1
    eqeq12d
    imbi2d
    @27
    @1
    wceq
    #
    @34
    @26
    wph
    @40
    @32
    @4
    @33
    @6
    @27
    @1
    @2
    @3
    oveq1
    @27
    @1
    @2
    @0
    oveq2
    eqeq12d
    imbi2d
    @28
    cY
    wcel
    #
    @27
    cX
    wcel
    #
    wa
    #
    wph
    @12
    @31
    @13
    @43
    @12
    wph
    @12
    vy
    vx
    cY
    cX
    rsp2
    @22
    syl11
    @41
    @42
    @12
    @31
    @41
    @42
    @12
    w3a
    @29
    cA
    @30
    @42
    @41
    @12
    @29
    cA
    wceq
    vx
    vy
    cX
    cY
    cA
    @3
    @10
    @21
    ovmpt4g
    3com12
    vy
    vx
    cY
    cX
    cA
    @0
    @10
    @23
    ovmpt4g
    eqtr4d
    3expia
    syld
    vtocl2gaf
    com12
    3impib
    mpt2eq3dva
    eqtr4d
    wph
    vz
    vw
    @1
    @2
    @3
    cK
    cJ
    cJ
    cK
    cL
    cY
    cX
    cnmptcom.4
    cnmptcom.3
    wph
    vz
    vw
    cK
    cJ
    cY
    cX
    cnmptcom.4
    cnmptcom.3
    cnmpt2nd
    wph
    vz
    vw
    cK
    cJ
    cY
    cX
    cnmptcom.4
    cnmptcom.3
    cnmpt1st
    cnmptcom.6
    cnmpt22f
    eqeltrd
end
