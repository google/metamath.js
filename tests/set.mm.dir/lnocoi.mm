include "ccom.mm"
include "wcel.mm"
include "cba.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cns.mm"
include "co.mm"
include "cpv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "cnv.mm"
include "eqid.mm"
include "lnof.mm"
include "mp3an.mm"
include "fco.mm"
include "mp2an.mm"
include "w3a.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "nvgcl.mm"
include "stoic3.mm"
include "fvco3.mm"
include "sylancr.mm"
include "id.mm"
include "ffvelrni.mm"
include "3pm3.2i.mm"
include "lnolin.mm"
include "mpan.mm"
include "syl3an.mm"
include "fveq2d.mm"
include "simp2.mm"
include "oveq2d.mm"
include "simp3.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "eqtr4d.mm"
include "rgen3.mm"
include "wa.mm"
include "wb.mm"
include "islno.mm"
include "mpbir2an.mm"

theorem lnocoi
  let cS: class S
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnocoi.l: |- L = ( U LnOp W )
  assume lnocoi.m: |- M = ( W LnOp X )
  assume lnocoi.n: |- N = ( U LnOp X )
  assume lnocoi.u: |- U e. NrmCVec
  assume lnocoi.w: |- W e. NrmCVec
  assume lnocoi.x: |- X e. NrmCVec
  assume lnocoi.s: |- S e. L
  assume lnocoi.t: |- T e. M


  assert |- ( T o. S ) e. N

  proof
    cT
    cS
    ccom
    #
    cN
    wcel
    #
    cU
    cba
    cfv
    #
    cX
    cba
    cfv
    #
    @0
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    #
    vz
    cv
    #
    cU
    cpv
    cfv
    #
    co
    #
    @0
    cfv
    #
    @5
    @6
    @0
    cfv
    #
    cX
    cns
    cfv
    #
    co
    #
    @9
    @0
    cfv
    #
    cX
    cpv
    cfv
    #
    co
    #
    wceq
    #
    vz
    @2
    wral
    vy
    @2
    wral
    vx
    cc
    wral
    #
    cW
    cba
    cfv
    #
    @3
    cT
    wf
    #
    @2
    @21
    cS
    wf
    #
    @4
    cW
    cnv
    wcel
    #
    cX
    cnv
    wcel
    #
    cT
    cM
    wcel
    #
    @22
    lnocoi.w
    lnocoi.x
    lnocoi.t
    cT
    cW
    cM
    cX
    @21
    @3
    @21
    eqid
    #
    @3
    eqid
    #
    lnocoi.m
    lnof
    mp3an
    cU
    cnv
    wcel
    #
    @24
    cS
    cL
    wcel
    #
    @23
    lnocoi.u
    lnocoi.w
    lnocoi.s
    cS
    cU
    cL
    cW
    @2
    @21
    @2
    eqid
    #
    @27
    lnocoi.l
    lnof
    mp3an
    #
    @2
    @21
    @3
    cT
    cS
    fco
    mp2an
    @19
    vx
    vy
    vz
    cc
    @2
    @2
    @5
    cc
    wcel
    #
    @6
    @2
    wcel
    #
    @9
    @2
    wcel
    #
    w3a
    #
    @12
    @11
    cS
    cfv
    #
    cT
    cfv
    #
    @18
    @36
    @23
    @11
    @2
    wcel
    #
    @12
    @38
    wceq
    @32
    @33
    @34
    @8
    @2
    wcel
    #
    @35
    @39
    @29
    @33
    @34
    @40
    lnocoi.u
    @5
    @6
    @7
    cU
    @2
    @31
    @7
    eqid
    #
    nvscl
    mp3an1
    @29
    @40
    @35
    @39
    lnocoi.u
    @8
    @9
    cU
    @10
    @2
    @31
    @10
    eqid
    #
    nvgcl
    mp3an1
    stoic3
    @2
    @21
    @11
    cT
    cS
    fvco3
    sylancr
    @36
    @5
    @6
    cS
    cfv
    #
    cW
    cns
    cfv
    #
    co
    @9
    cS
    cfv
    #
    cW
    cpv
    cfv
    #
    co
    #
    cT
    cfv
    #
    @5
    @43
    cT
    cfv
    #
    @14
    co
    #
    @45
    cT
    cfv
    #
    @17
    co
    #
    @38
    @18
    @33
    @33
    @34
    @43
    @21
    wcel
    #
    @35
    @45
    @21
    wcel
    #
    @48
    @52
    wceq
    #
    @33
    id
    @2
    @21
    @6
    cS
    @32
    ffvelrni
    @2
    @21
    @9
    cS
    @32
    ffvelrni
    @24
    @25
    @26
    w3a
    @33
    @53
    @54
    w3a
    @55
    @24
    @25
    @26
    lnocoi.w
    lnocoi.x
    lnocoi.t
    3pm3.2i
    @5
    @43
    @45
    @44
    @14
    cT
    cW
    @46
    @17
    cM
    cX
    @21
    @3
    @27
    @28
    @46
    eqid
    #
    @17
    eqid
    #
    @44
    eqid
    #
    @14
    eqid
    #
    lnocoi.m
    lnolin
    mpan
    syl3an
    @36
    @37
    @47
    cT
    @29
    @24
    @30
    w3a
    @36
    @37
    @47
    wceq
    @29
    @24
    @30
    lnocoi.u
    lnocoi.w
    lnocoi.s
    3pm3.2i
    @5
    @6
    @9
    @7
    @44
    cS
    cU
    @10
    @46
    cL
    cW
    @2
    @21
    @31
    @27
    @42
    @56
    @41
    @58
    lnocoi.l
    lnolin
    mpan
    fveq2d
    @36
    @15
    @50
    @16
    @51
    @17
    @36
    @13
    @49
    @5
    @14
    @36
    @23
    @34
    @13
    @49
    wceq
    @32
    @33
    @34
    @35
    simp2
    @2
    @21
    @6
    cT
    cS
    fvco3
    sylancr
    oveq2d
    @36
    @23
    @35
    @16
    @51
    wceq
    @32
    @33
    @34
    @35
    simp3
    @2
    @21
    @9
    cT
    cS
    fvco3
    sylancr
    oveq12d
    3eqtr4rd
    eqtr4d
    rgen3
    @29
    @25
    @1
    @4
    @20
    wa
    wb
    lnocoi.u
    lnocoi.x
    vx
    vy
    vz
    @7
    @14
    @0
    cU
    @10
    @17
    cN
    cX
    @2
    @3
    @31
    @28
    @42
    @57
    @41
    @59
    lnocoi.n
    islno
    mp2an
    mpbir2an
end
