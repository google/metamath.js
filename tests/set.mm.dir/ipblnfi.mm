include "wcel.mm"
include "clno.mm"
include "co.mm"
include "cnmcv.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cc.mm"
include "wf.mm"
include "cns.mm"
include "cpv.mm"
include "caddc.mm"
include "wceq.mm"
include "cnv.mm"
include "phnvi.mm"
include "dipcl.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "fmptd.mm"
include "wa.mm"
include "eqid.mm"
include "nvscl.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "simpll.mm"
include "ccphlo.mm"
include "w3a.mm"
include "dipdir.mm"
include "mpan.mm"
include "syl3anc.mm"
include "simplr.mm"
include "simprl.mm"
include "ipassi.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "adantll.mm"
include "nvgcl.mm"
include "sylan.mm"
include "anasss.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "ad2antrl.mm"
include "oveq2d.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cnnv.mm"
include "cnnvba.mm"
include "cnnvg.mm"
include "cnnvs.mm"
include "islno.mm"
include "mp2an.mm"
include "sylanbrc.mm"
include "nvcl.mm"
include "sii.mm"
include "adantl.mm"
include "fveq2d.mm"
include "recnd.mm"
include "mulcom.mm"
include "syl2an.mm"
include "3brtr4d.mm"
include "cnnvnm.mm"
include "blo3i.mm"

theorem ipblnfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cF: class F
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ipblnfi.1: |- X = ( BaseSet ` U )
  assume ipblnfi.7: |- P = ( .iOLD ` U )
  assume ipblnfi.9: |- U e. CPreHilOLD
  assume ipblnfi.c: |- C = <. <. + , x. >. , abs >.
  assume ipblnfi.l: |- B = ( U BLnOp C )
  assume ipblnfi.f: |- F = ( x e. X |-> ( x P A ) )

  disjoint A x
  disjoint U x
  disjoint X x
  disjoint P x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint B z
  assert |- ( A e. X -> F e. B )

  proof
    cA
    cX
    wcel
    #
    cF
    cU
    cC
    clno
    co
    #
    wcel
    #
    cA
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cr
    wcel
    #
    vz
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @4
    @6
    @3
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    cF
    cB
    wcel
    @0
    cX
    cc
    cF
    wf
    #
    vy
    cv
    #
    @6
    cU
    cns
    cfv
    #
    co
    #
    vw
    cv
    #
    cU
    cpv
    cfv
    #
    co
    #
    cF
    cfv
    #
    @13
    @7
    cmul
    co
    #
    @16
    cF
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vw
    cX
    wral
    vz
    cX
    wral
    #
    vy
    cc
    wral
    #
    @2
    @0
    vx
    cX
    vx
    cv
    #
    cA
    cP
    co
    #
    cc
    cF
    @26
    cX
    wcel
    #
    @0
    @27
    cc
    wcel
    #
    cU
    cnv
    wcel
    #
    @28
    @0
    @29
    cU
    ipblnfi.9
    phnvi
    #
    @26
    cA
    cP
    cU
    cX
    ipblnfi.1
    ipblnfi.7
    dipcl
    mp3an1
    ancoms
    ipblnfi.f
    fmptd
    @0
    @24
    vy
    cc
    @0
    @13
    cc
    wcel
    #
    wa
    #
    @23
    vz
    vw
    cX
    cX
    @33
    @6
    cX
    wcel
    #
    @16
    cX
    wcel
    #
    wa
    #
    wa
    #
    @18
    cA
    cP
    co
    #
    @13
    @6
    cA
    cP
    co
    #
    cmul
    co
    #
    @16
    cA
    cP
    co
    #
    caddc
    co
    #
    @19
    @22
    @37
    @38
    @15
    cA
    cP
    co
    #
    @41
    caddc
    co
    #
    @42
    @37
    @15
    cX
    wcel
    #
    @35
    @0
    @38
    @44
    wceq
    #
    @32
    @34
    @45
    @0
    @35
    @30
    @32
    @34
    @45
    @31
    @13
    @6
    @14
    cU
    cX
    ipblnfi.1
    @14
    eqid
    #
    nvscl
    mp3an1
    #
    ad2ant2lr
    @33
    @34
    @35
    simprr
    @0
    @32
    @36
    simpll
    #
    cU
    ccphlo
    wcel
    @45
    @35
    @0
    w3a
    @46
    ipblnfi.9
    @15
    @16
    cA
    cP
    cU
    @17
    cX
    ipblnfi.1
    @17
    eqid
    #
    ipblnfi.7
    dipdir
    mpan
    syl3anc
    @37
    @43
    @40
    @41
    caddc
    @37
    @32
    @34
    @0
    @43
    @40
    wceq
    @0
    @32
    @36
    simplr
    @33
    @34
    @35
    simprl
    @49
    @13
    @6
    cA
    cP
    @14
    cU
    @17
    cX
    ipblnfi.1
    @50
    @47
    ipblnfi.7
    ipblnfi.9
    ipassi
    syl3anc
    oveq1d
    eqtrd
    @37
    @18
    cX
    wcel
    #
    @19
    @38
    wceq
    @33
    @34
    @35
    @51
    @33
    @34
    wa
    @45
    @35
    @51
    @32
    @34
    @45
    @0
    @48
    adantll
    @30
    @45
    @35
    @51
    @31
    @15
    @16
    cU
    @17
    cX
    ipblnfi.1
    @50
    nvgcl
    mp3an1
    sylan
    anasss
    vx
    @18
    @27
    @38
    cX
    cF
    @26
    @18
    cA
    cP
    oveq1
    ipblnfi.f
    @18
    cA
    cP
    ovex
    fvmpt
    syl
    @37
    @20
    @40
    @21
    @41
    caddc
    @37
    @7
    @39
    @13
    cmul
    @34
    @7
    @39
    wceq
    #
    @33
    @35
    vx
    @6
    @27
    @39
    cX
    cF
    @26
    @6
    cA
    cP
    oveq1
    ipblnfi.f
    @6
    cA
    cP
    ovex
    fvmpt
    #
    ad2antrl
    oveq2d
    @35
    @21
    @41
    wceq
    @33
    @34
    vx
    @16
    @27
    @41
    cX
    cF
    @26
    @16
    cA
    cP
    oveq1
    ipblnfi.f
    @16
    cA
    cP
    ovex
    fvmpt
    ad2antll
    oveq12d
    3eqtr4d
    ralrimivva
    ralrimiva
    @30
    cC
    cnv
    wcel
    @2
    @12
    @25
    wa
    wb
    @31
    cC
    ipblnfi.c
    cnnv
    #
    vy
    vz
    vw
    @14
    cmul
    cF
    cU
    @17
    caddc
    @1
    cC
    cX
    cc
    ipblnfi.1
    cC
    ipblnfi.c
    cnnvba
    @50
    cC
    ipblnfi.c
    cnnvg
    @47
    cC
    ipblnfi.c
    cnnvs
    @1
    eqid
    #
    islno
    mp2an
    sylanbrc
    @30
    @0
    @5
    @31
    cA
    cU
    @3
    cX
    ipblnfi.1
    @3
    eqid
    #
    nvcl
    mpan
    #
    @0
    @11
    vz
    cX
    @0
    @34
    wa
    #
    @39
    cabs
    cfv
    #
    @9
    @4
    cmul
    co
    #
    @8
    @10
    cle
    @34
    @0
    @59
    @60
    cle
    wbr
    @6
    cA
    cP
    cU
    @3
    cX
    ipblnfi.1
    @56
    ipblnfi.7
    ipblnfi.9
    sii
    ancoms
    @58
    @7
    @39
    cabs
    @34
    @52
    @0
    @53
    adantl
    fveq2d
    @0
    @4
    cc
    wcel
    @9
    cc
    wcel
    @10
    @60
    wceq
    @34
    @0
    @4
    @57
    recnd
    @34
    @9
    @30
    @34
    @9
    cr
    wcel
    @31
    @6
    cU
    @3
    cX
    ipblnfi.1
    @56
    nvcl
    mpan
    recnd
    @4
    @9
    mulcom
    syl2an
    3brtr4d
    ralrimiva
    vz
    @4
    cB
    cF
    cU
    @1
    @3
    cabs
    cC
    cX
    ipblnfi.1
    @56
    cC
    ipblnfi.c
    cnnvnm
    @55
    ipblnfi.l
    @31
    @54
    blo3i
    syl3anc
end
