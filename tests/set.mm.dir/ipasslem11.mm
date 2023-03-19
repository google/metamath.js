include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cnre.mm"
include "wa.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcom.mm"
include "sylancr.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "cnv.mm"
include "phnvi.mm"
include "nvscl.mm"
include "mp3an13.mm"
include "syl.mm"
include "mulcl.mm"
include "sylancl.mm"
include "ipdiri.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "ipasslem9.mm"
include "mp3an.mm"
include "w3a.mm"
include "nvsass.mm"
include "mpan.mm"
include "mp3an23.mm"
include "oveq1d.mm"
include "dipcl.mm"
include "mulass.mm"
include "cnmcv.mm"
include "cfv.mm"
include "eqid.mm"
include "ipasslem10.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "3eqtr4d.mm"
include "oveqan12d.mm"
include "eqtrd.mm"
include "nvdir.mm"
include "adddir.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "rexlimivv.mm"

theorem ipasslem11
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem11.a: |- A e. X
  assume ipasslem11.b: |- B e. X


  assert |- ( C e. CC -> ( ( C S A ) P B ) = ( C x. ( A P B ) ) )

  proof
    cC
    cc
    wcel
    cC
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    cC
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cC
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    vx
    vy
    cC
    cnre
    @4
    @9
    vx
    vy
    cr
    cr
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @4
    cC
    @0
    @1
    ci
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @9
    @12
    @3
    @14
    cC
    @12
    @2
    @13
    @0
    caddc
    @11
    @2
    @13
    wceq
    #
    @10
    @11
    ci
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @16
    ax-icn
    @1
    recn
    #
    ci
    @1
    mulcom
    sylancr
    adantl
    oveq2d
    eqeq2d
    @12
    @9
    @15
    @14
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @14
    @7
    cmul
    co
    #
    wceq
    @12
    @0
    cA
    cS
    co
    #
    @13
    cA
    cS
    co
    #
    cG
    co
    #
    cB
    cP
    co
    #
    @0
    @7
    cmul
    co
    #
    @13
    @7
    cmul
    co
    #
    caddc
    co
    #
    @21
    @22
    @12
    @26
    @23
    cB
    cP
    co
    #
    @24
    cB
    cP
    co
    #
    caddc
    co
    #
    @29
    @10
    @23
    cX
    wcel
    #
    @24
    cX
    wcel
    #
    @26
    @32
    wceq
    #
    @11
    @10
    @0
    cc
    wcel
    #
    @33
    @0
    recn
    #
    cU
    cnv
    wcel
    #
    @36
    cA
    cX
    wcel
    #
    @33
    cU
    ip1i.9
    phnvi
    #
    ipasslem11.a
    @0
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an13
    syl
    @11
    @13
    cc
    wcel
    #
    @34
    @11
    @18
    @17
    @41
    @19
    ax-icn
    @1
    ci
    mulcl
    sylancl
    #
    @38
    @41
    @39
    @34
    @40
    ipasslem11.a
    @13
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an13
    syl
    @33
    @34
    cB
    cX
    wcel
    #
    @35
    ipasslem11.b
    @23
    @24
    cB
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipdiri
    mp3an3
    syl2an
    @10
    @11
    @30
    @27
    @31
    @28
    caddc
    cA
    cB
    @0
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem11.a
    ipasslem11.b
    ipasslem9
    @11
    @1
    ci
    cA
    cS
    co
    #
    cS
    co
    #
    cB
    cP
    co
    @1
    @44
    cB
    cP
    co
    #
    cmul
    co
    #
    @31
    @28
    @44
    cB
    @1
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    @38
    @17
    @39
    @44
    cX
    wcel
    @40
    ax-icn
    ipasslem11.a
    ci
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an
    ipasslem11.b
    ipasslem9
    @11
    @24
    @45
    cB
    cP
    @11
    @18
    @24
    @45
    wceq
    #
    @19
    @18
    @17
    @39
    @48
    ax-icn
    ipasslem11.a
    @38
    @18
    @17
    @39
    w3a
    @48
    @40
    @1
    ci
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsass
    mpan
    mp3an23
    syl
    oveq1d
    @11
    @28
    @1
    ci
    @7
    cmul
    co
    #
    cmul
    co
    #
    @47
    @11
    @18
    @28
    @50
    wceq
    #
    @19
    @18
    @17
    @7
    cc
    wcel
    #
    @51
    ax-icn
    @38
    @39
    @43
    @52
    @40
    ipasslem11.a
    ipasslem11.b
    cA
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an
    #
    @1
    ci
    @7
    mulass
    mp3an23
    syl
    @46
    @49
    @1
    cmul
    cA
    cB
    cP
    cS
    cU
    cG
    cU
    cnmcv
    cfv
    #
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem11.a
    ipasslem11.b
    @54
    eqid
    ipasslem10
    oveq2i
    syl6eqr
    3eqtr4d
    oveqan12d
    eqtrd
    @12
    @20
    @25
    cB
    cP
    @10
    @36
    @41
    @20
    @25
    wceq
    #
    @11
    @37
    @42
    @36
    @41
    @39
    @55
    ipasslem11.a
    @38
    @36
    @41
    @39
    w3a
    @55
    @40
    @0
    @13
    cA
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    nvdir
    mpan
    mp3an3
    syl2an
    oveq1d
    @10
    @36
    @41
    @22
    @29
    wceq
    #
    @11
    @37
    @42
    @36
    @41
    @52
    @56
    @53
    @0
    @13
    @7
    adddir
    mp3an3
    syl2an
    3eqtr4d
    @15
    @6
    @21
    @8
    @22
    @15
    @5
    @20
    cB
    cP
    cC
    @14
    cA
    cS
    oveq1
    oveq1d
    cC
    @14
    @7
    cmul
    oveq1
    eqeq12d
    syl5ibrcom
    sylbid
    rexlimivv
    syl
end
