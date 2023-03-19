include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "ccxp.mm"
include "co.mm"
include "chash.mm"
include "cdiv.mm"
include "cmul.mm"
include "cbs.mm"
include "cc.mm"
include "eqid.mm"
include "dchrf.mm"
include "unitss.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "cc0.mm"
include "wne.mm"
include "wcel.mm"
include "dchrn0.mm"
include "mpbird.mm"
include "absrpcld.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "cn.mm"
include "dchrrcl.mm"
include "znfi.mm"
include "3syl.mm"
include "ssfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "recnd.mm"
include "c0.mm"
include "ne0i.mm"
include "wb.mm"
include "hashnncl.mm"
include "nnne0d.mm"
include "reccld.mm"
include "cxpmuld.mm"
include "recidd.mm"
include "oveq2d.mm"
include "cexp.mm"
include "wceq.mm"
include "abscld.mm"
include "cxpexp.mm"
include "syl2anc.mm"
include "absexpd.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cmg.mm"
include "cur.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "cres.mm"
include "csubmnd.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "unitsubm.mm"
include "mp1i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "submmulg.mm"
include "syl3anc.mm"
include "cghm.mm"
include "cz.mm"
include "dchrghm.mm"
include "nn0zd.mm"
include "unitgrpbas.mm"
include "ghmmulg.mm"
include "c0g.mm"
include "cod.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgrp.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "unitgrp.mm"
include "oddvds2.mm"
include "oddvds.mm"
include "mpbid.mm"
include "unitgrpid.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "fvres.mm"
include "3eqtr3d.mm"
include "1unit.mm"
include "3eqtr2d.mm"
include "cnfldexp.mm"
include "cmhm.mm"
include "dchrmhm.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "abs1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cxp1d.mm"
include "1cxpd.mm"

theorem dchrabs
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume dchrabs.g: |- G = ( DChr ` N )
  assume dchrabs.d: |- D = ( Base ` G )
  assume dchrabs.x: |- ( ph -> X e. D )
  assume dchrabs.z: |- Z = ( Z/nZ ` N )
  assume dchrabs.u: |- U = ( Unit ` Z )
  assume dchrabs.a: |- ( ph -> A e. U )


  assert |- ( ph -> ( abs ` ( X ` A ) ) = 1 )

  proof
    wph
    cA
    cX
    cfv
    #
    cabs
    cfv
    #
    c1
    ccxp
    co
    #
    c1
    c1
    cU
    chash
    cfv
    #
    cdiv
    co
    #
    ccxp
    co
    #
    @1
    c1
    wph
    @1
    @3
    @4
    cmul
    co
    #
    ccxp
    co
    @1
    @3
    ccxp
    co
    #
    @4
    ccxp
    co
    @2
    @5
    wph
    @1
    @3
    @4
    wph
    @0
    wph
    cZ
    cbs
    cfv
    #
    cc
    cA
    cX
    wph
    @8
    cD
    cG
    cN
    cX
    cZ
    dchrabs.g
    dchrabs.z
    dchrabs.d
    @8
    eqid
    #
    dchrabs.x
    dchrf
    wph
    cU
    @8
    cA
    @8
    cZ
    cU
    @9
    dchrabs.u
    unitss
    #
    dchrabs.a
    sseldi
    #
    ffvelrnd
    #
    wph
    @0
    cc0
    wne
    #
    cA
    cU
    wcel
    #
    dchrabs.a
    wph
    cA
    @8
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrabs.g
    dchrabs.z
    dchrabs.d
    @9
    dchrabs.u
    dchrabs.x
    @11
    dchrn0
    mpbird
    #
    absrpcld
    wph
    @3
    wph
    cU
    cfn
    wcel
    #
    @3
    cn0
    wcel
    #
    wph
    @8
    cfn
    wcel
    #
    cU
    @8
    wss
    @16
    wph
    cX
    cD
    wcel
    #
    cN
    cn
    wcel
    #
    @18
    dchrabs.x
    cD
    cG
    cN
    cX
    dchrabs.g
    dchrabs.d
    dchrrcl
    #
    @8
    cN
    cZ
    dchrabs.z
    @9
    znfi
    3syl
    @10
    @8
    cU
    ssfi
    sylancl
    #
    cU
    hashcl
    syl
    #
    nn0red
    #
    wph
    @3
    wph
    @3
    @24
    recnd
    #
    wph
    @3
    wph
    @3
    cn
    wcel
    #
    cU
    c0
    wne
    #
    wph
    @14
    @27
    dchrabs.a
    cU
    cA
    ne0i
    syl
    wph
    @16
    @26
    @27
    wb
    @22
    cU
    hashnncl
    syl
    mpbird
    nnne0d
    #
    reccld
    #
    cxpmuld
    wph
    @6
    c1
    @1
    ccxp
    wph
    @3
    @25
    @28
    recidd
    oveq2d
    wph
    @7
    c1
    @4
    ccxp
    wph
    @7
    @1
    @3
    cexp
    co
    #
    @0
    @3
    cexp
    co
    #
    cabs
    cfv
    #
    c1
    wph
    @1
    cc
    wcel
    @17
    @7
    @30
    wceq
    wph
    @1
    wph
    @0
    @12
    abscld
    recnd
    #
    @23
    @1
    @3
    cxpexp
    syl2anc
    wph
    @0
    @3
    @12
    @23
    absexpd
    wph
    @32
    c1
    cabs
    cfv
    c1
    wph
    @31
    c1
    cabs
    wph
    @3
    @0
    ccnfld
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    @31
    c1
    wph
    @36
    @3
    @0
    @34
    cc
    cc0
    csn
    cdif
    #
    cress
    co
    #
    cmg
    cfv
    #
    co
    #
    @37
    cX
    cU
    cres
    #
    cfv
    #
    @38
    wph
    @39
    @34
    csubmnd
    cfv
    wcel
    #
    @17
    @0
    @39
    wcel
    #
    @36
    @42
    wceq
    ccnfld
    crg
    wcel
    @45
    wph
    cnring
    ccnfld
    @39
    @34
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @34
    eqid
    #
    unitsubm
    mp1i
    @23
    wph
    @0
    cc
    wcel
    #
    @13
    @46
    @12
    @15
    @0
    cc
    cc0
    eldifsn
    sylanbrc
    @39
    @35
    @41
    @34
    @40
    @3
    @0
    @35
    eqid
    @40
    eqid
    #
    @41
    eqid
    #
    submmulg
    syl3anc
    wph
    @3
    cA
    cZ
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    cmg
    cfv
    #
    co
    #
    @43
    cfv
    #
    @3
    cA
    @43
    cfv
    #
    @41
    co
    #
    @44
    @42
    wph
    @43
    @52
    @40
    cghm
    co
    wcel
    @3
    cz
    wcel
    #
    @14
    @55
    @57
    wceq
    wph
    cD
    cU
    cG
    @52
    @40
    cN
    cX
    cZ
    dchrabs.g
    dchrabs.z
    dchrabs.d
    dchrabs.u
    @52
    eqid
    #
    @49
    dchrabs.x
    dchrghm
    wph
    @3
    @23
    nn0zd
    #
    dchrabs.a
    cU
    @53
    @41
    @43
    @52
    @40
    @3
    cA
    cZ
    cU
    @52
    dchrabs.u
    @59
    unitgrpbas
    #
    @53
    eqid
    #
    @50
    ghmmulg
    syl3anc
    wph
    @54
    @37
    @43
    wph
    @54
    @52
    c0g
    cfv
    #
    @37
    wph
    cA
    @52
    cod
    cfv
    #
    cfv
    @3
    cdvds
    wbr
    #
    @54
    @63
    wceq
    #
    wph
    @52
    cgrp
    wcel
    #
    @16
    @14
    @65
    wph
    cZ
    crg
    wcel
    #
    @67
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @68
    wph
    cN
    wph
    @19
    @20
    dchrabs.x
    @21
    syl
    nnnn0d
    cN
    cZ
    dchrabs.z
    zncrng
    cZ
    crngring
    3syl
    #
    cZ
    cU
    @52
    dchrabs.u
    @59
    unitgrp
    syl
    #
    @22
    dchrabs.a
    cA
    @52
    @64
    cU
    @61
    @64
    eqid
    #
    oddvds2
    syl3anc
    wph
    @67
    @14
    @58
    @65
    @66
    wb
    @70
    dchrabs.a
    @60
    cA
    @53
    @52
    @3
    @64
    cU
    @63
    @61
    @71
    @62
    @63
    eqid
    oddvds
    syl3anc
    mpbid
    wph
    @68
    @37
    @63
    wceq
    @69
    cZ
    cU
    @37
    @52
    dchrabs.u
    @59
    @37
    eqid
    #
    unitgrpid
    syl
    eqtr4d
    fveq2d
    wph
    @56
    @0
    @3
    @41
    wph
    @14
    @56
    @0
    wceq
    dchrabs.a
    cA
    cU
    cX
    fvres
    syl
    oveq2d
    3eqtr3d
    wph
    @68
    @37
    cU
    wcel
    @44
    @38
    wceq
    @69
    cZ
    cU
    @37
    dchrabs.u
    @72
    1unit
    @37
    cU
    cX
    fvres
    3syl
    3eqtr2d
    wph
    @48
    @17
    @36
    @31
    wceq
    @12
    @23
    @0
    @3
    cnfldexp
    syl2anc
    wph
    cX
    @51
    @34
    cmhm
    co
    #
    wcel
    @38
    c1
    wceq
    wph
    cD
    @73
    cX
    cD
    cG
    cN
    cZ
    dchrabs.g
    dchrabs.z
    dchrabs.d
    dchrmhm
    dchrabs.x
    sseldi
    @51
    @34
    cX
    c1
    @37
    cZ
    @37
    @51
    @51
    eqid
    @72
    ringidval
    ccnfld
    c1
    @34
    @47
    cnfld1
    ringidval
    mhm0
    syl
    3eqtr3d
    fveq2d
    abs1
    syl6eq
    3eqtr2d
    oveq1d
    3eqtr3d
    wph
    @1
    @33
    cxp1d
    wph
    @4
    @29
    1cxpd
    3eqtr3d
end
