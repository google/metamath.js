include "cba.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "imsdf.mm"
include "ax-mp.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "imsdval2.mm"
include "mp3an1.mm"
include "eqeq1d.mm"
include "wb.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an12.mm"
include "nvgcl.mm"
include "sylan2.mm"
include "nvz.mm"
include "sylancr.mm"
include "nvzcl.mm"
include "w3a.mm"
include "nvrcan.mm"
include "mpan.mm"
include "mp3an2.mm"
include "sylancom.mm"
include "simpl.mm"
include "adantl.mm"
include "simpr.mm"
include "nvass.mm"
include "syl3anc.mm"
include "nvlinv.mm"
include "oveq2d.mm"
include "nv0rid.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "nv0lid.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "3bitrd.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3adant2.mm"
include "nvtri.mm"
include "3adant1.mm"
include "simp1.mm"
include "3ad2ant3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "nvdif.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "3coml.mm"
include "ismeti.mm"

theorem imsmetlem
  let cD: class D
  let cS: class S
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume imsmetlem.1: |- X = ( BaseSet ` U )
  assume imsmetlem.2: |- G = ( +v ` U )
  assume imsmetlem.7: |- M = ( inv ` G )
  assume imsmetlem.4: |- S = ( .sOLD ` U )
  assume imsmetlem.5: |- Z = ( 0vec ` U )
  assume imsmetlem.6: |- N = ( normCV ` U )
  assume imsmetlem.8: |- D = ( IndMet ` U )
  assume imsmetlem.9: |- U e. NrmCVec


  assert |- D e. ( Met ` X )

  proof
    vx
    vy
    vz
    cD
    cX
    cX
    cU
    cba
    cfv
    cvv
    imsmetlem.1
    cU
    cba
    fvex
    eqeltri
    cU
    cnv
    wcel
    #
    cX
    cX
    cxp
    cr
    cD
    wf
    imsmetlem.9
    cD
    cU
    cX
    imsmetlem.1
    imsmetlem.8
    imsdf
    ax-mp
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    wa
    #
    @1
    @3
    cD
    co
    #
    cc0
    wceq
    @1
    c1
    cneg
    #
    @3
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @9
    cZ
    wceq
    #
    @1
    @3
    wceq
    #
    @5
    @6
    @10
    cc0
    @0
    @2
    @4
    @6
    @10
    wceq
    #
    imsmetlem.9
    @1
    @3
    cD
    cS
    cU
    cG
    cN
    cX
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.6
    imsmetlem.8
    imsdval2
    mp3an1
    #
    eqeq1d
    @5
    @0
    @9
    cX
    wcel
    #
    @11
    @12
    wb
    imsmetlem.9
    @4
    @2
    @8
    cX
    wcel
    #
    @16
    @0
    @7
    cc
    wcel
    #
    @4
    @17
    imsmetlem.9
    neg1cn
    @7
    @3
    cS
    cU
    cX
    imsmetlem.1
    imsmetlem.4
    nvscl
    mp3an12
    #
    @0
    @2
    @17
    @16
    imsmetlem.9
    @1
    @8
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvgcl
    mp3an1
    sylan2
    #
    @9
    cU
    cN
    cX
    cZ
    imsmetlem.1
    imsmetlem.5
    imsmetlem.6
    nvz
    sylancr
    @5
    @9
    @3
    cG
    co
    #
    cZ
    @3
    cG
    co
    #
    wceq
    #
    @12
    @13
    @2
    @4
    @16
    @23
    @12
    wb
    #
    @20
    @16
    cZ
    cX
    wcel
    #
    @4
    @24
    @0
    @25
    imsmetlem.9
    cU
    cX
    cZ
    imsmetlem.1
    imsmetlem.5
    nvzcl
    ax-mp
    @0
    @16
    @25
    @4
    w3a
    @24
    imsmetlem.9
    @9
    cZ
    @3
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvrcan
    mpan
    mp3an2
    sylancom
    @5
    @21
    @1
    @22
    @3
    @5
    @21
    @1
    @8
    @3
    cG
    co
    #
    cG
    co
    #
    @1
    cZ
    cG
    co
    #
    @1
    @5
    @2
    @17
    @4
    @21
    @27
    wceq
    #
    @2
    @4
    simpl
    @4
    @17
    @2
    @19
    adantl
    @2
    @4
    simpr
    @0
    @2
    @17
    @4
    w3a
    @29
    imsmetlem.9
    @1
    @8
    @3
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvass
    mpan
    syl3anc
    @5
    @26
    cZ
    @1
    cG
    @4
    @26
    cZ
    wceq
    #
    @2
    @0
    @4
    @30
    imsmetlem.9
    @3
    cS
    cU
    cG
    cX
    cZ
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.5
    nvlinv
    mpan
    adantl
    oveq2d
    @2
    @28
    @1
    wceq
    #
    @4
    @0
    @2
    @31
    imsmetlem.9
    @1
    cU
    cG
    cX
    cZ
    imsmetlem.1
    imsmetlem.2
    imsmetlem.5
    nv0rid
    mpan
    #
    adantr
    3eqtrd
    @4
    @22
    @3
    wceq
    #
    @2
    @0
    @4
    @33
    imsmetlem.9
    @3
    cU
    cG
    cX
    cZ
    imsmetlem.1
    imsmetlem.2
    imsmetlem.5
    nv0lid
    mpan
    adantl
    eqeq12d
    bitr3d
    3bitrd
    vz
    cv
    #
    cX
    wcel
    #
    @2
    @4
    @6
    @34
    @1
    cD
    co
    #
    @34
    @3
    cD
    co
    #
    caddc
    co
    #
    cle
    wbr
    @35
    @2
    @4
    w3a
    #
    @1
    @7
    @34
    cS
    co
    #
    cG
    co
    #
    @34
    @8
    cG
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    @41
    cN
    cfv
    #
    @42
    cN
    cfv
    #
    caddc
    co
    #
    @6
    @38
    cle
    @39
    @41
    cX
    wcel
    #
    @42
    cX
    wcel
    #
    @44
    @47
    cle
    wbr
    #
    @35
    @2
    @48
    @4
    @35
    @2
    wa
    #
    @2
    @40
    cX
    wcel
    #
    @48
    @35
    @2
    simpr
    #
    @35
    @52
    @2
    @0
    @18
    @35
    @52
    imsmetlem.9
    neg1cn
    @7
    @34
    cS
    cU
    cX
    imsmetlem.1
    imsmetlem.4
    nvscl
    mp3an12
    adantr
    #
    @0
    @2
    @52
    @48
    imsmetlem.9
    @1
    @40
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvgcl
    mp3an1
    syl2anc
    3adant3
    #
    @35
    @4
    @49
    @2
    @4
    @35
    @17
    @49
    @19
    @0
    @35
    @17
    @49
    imsmetlem.9
    @34
    @8
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvgcl
    mp3an1
    sylan2
    3adant2
    @0
    @48
    @49
    @50
    imsmetlem.9
    @41
    @42
    cU
    cG
    cN
    cX
    imsmetlem.1
    imsmetlem.2
    imsmetlem.6
    nvtri
    mp3an1
    syl2anc
    @39
    @6
    @10
    @44
    @2
    @4
    @14
    @35
    @15
    3adant1
    @39
    @43
    @9
    cN
    @39
    @41
    @34
    cG
    co
    #
    @8
    cG
    co
    #
    @43
    @9
    @39
    @48
    @35
    @17
    @57
    @43
    wceq
    #
    @55
    @35
    @2
    @4
    simp1
    @4
    @35
    @17
    @2
    @19
    3ad2ant3
    @0
    @48
    @35
    @17
    w3a
    @58
    imsmetlem.9
    @41
    @34
    @8
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvass
    mpan
    syl3anc
    @39
    @56
    @1
    @8
    cG
    @35
    @2
    @56
    @1
    wceq
    @4
    @51
    @56
    @1
    @40
    @34
    cG
    co
    #
    cG
    co
    #
    @28
    @1
    @51
    @2
    @52
    @35
    @56
    @60
    wceq
    #
    @53
    @54
    @35
    @2
    simpl
    @0
    @2
    @52
    @35
    w3a
    @61
    imsmetlem.9
    @1
    @40
    @34
    cU
    cG
    cX
    imsmetlem.1
    imsmetlem.2
    nvass
    mpan
    syl3anc
    @51
    @59
    cZ
    @1
    cG
    @35
    @59
    cZ
    wceq
    #
    @2
    @0
    @35
    @62
    imsmetlem.9
    @34
    cS
    cU
    cG
    cX
    cZ
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.5
    nvlinv
    mpan
    adantr
    oveq2d
    @2
    @31
    @35
    @32
    adantl
    3eqtrd
    3adant3
    oveq1d
    eqtr3d
    fveq2d
    eqtr4d
    @39
    @36
    @45
    @37
    @46
    caddc
    @35
    @2
    @36
    @45
    wceq
    @4
    @51
    @36
    @34
    @7
    @1
    cS
    co
    cG
    co
    cN
    cfv
    #
    @45
    @0
    @35
    @2
    @36
    @63
    wceq
    imsmetlem.9
    @34
    @1
    cD
    cS
    cU
    cG
    cN
    cX
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.6
    imsmetlem.8
    imsdval2
    mp3an1
    @0
    @35
    @2
    @63
    @45
    wceq
    imsmetlem.9
    @34
    @1
    cS
    cU
    cG
    cN
    cX
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.6
    nvdif
    mp3an1
    eqtrd
    3adant3
    @35
    @4
    @37
    @46
    wceq
    #
    @2
    @0
    @35
    @4
    @64
    imsmetlem.9
    @34
    @3
    cD
    cS
    cU
    cG
    cN
    cX
    imsmetlem.1
    imsmetlem.2
    imsmetlem.4
    imsmetlem.6
    imsmetlem.8
    imsdval2
    mp3an1
    3adant2
    oveq12d
    3brtr4d
    3coml
    ismeti
end
