include "co.mm"
include "ccph.mm"
include "wcel.mm"
include "cc.mm"
include "cphipcl.mm"
include "syl3anc.mm"
include "rpred.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "subcld.mm"
include "abscld.mm"
include "cngp.mm"
include "cr.mm"
include "cnlm.mm"
include "cphnlm.mm"
include "syl.mm"
include "nlmngp.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nmge0.mm"
include "ge0p1rpd.mm"
include "cmt.mm"
include "ngpms.mm"
include "mscl.mm"
include "remulcld.mm"
include "rehalfcld.mm"
include "csg.mm"
include "wceq.mm"
include "eqid.mm"
include "cphsubdi.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpsubcl.mm"
include "ipcau.mm"
include "ngpds.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "eqbrtrrd.mm"
include "cxme.mm"
include "msxms.mm"
include "xmsge0.mm"
include "lep1d.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "clt.mm"
include "syl6breq.mm"
include "ltmuldiv2d.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "crp.mm"
include "rphalfcld.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "readdcld.mm"
include "cphsubdir.mm"
include "oveq1d.mm"
include "resubcld.mm"
include "nm2dif.mm"
include "ngpdsr.mm"
include "ltled.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "lemul2ad.mm"
include "wb.mm"
include "0red.mm"
include "ltaddrpd.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "abs3lemd.mm"

theorem ipcnlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cT: class T
  let cU: class U
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume ipcn.v: |- V = ( Base ` W )
  assume ipcn.h: |- ., = ( .i ` W )
  assume ipcn.d: |- D = ( dist ` W )
  assume ipcn.n: |- N = ( norm ` W )
  assume ipcn.t: |- T = ( ( R / 2 ) / ( ( N ` A ) + 1 ) )
  assume ipcn.u: |- U = ( ( R / 2 ) / ( ( N ` B ) + T ) )
  assume ipcn.w: |- ( ph -> W e. CPreHil )
  assume ipcn.a: |- ( ph -> A e. V )
  assume ipcn.b: |- ( ph -> B e. V )
  assume ipcn.r: |- ( ph -> R e. RR+ )
  assume ipcn.x: |- ( ph -> X e. V )
  assume ipcn.y: |- ( ph -> Y e. V )
  assume ipcn.1: |- ( ph -> ( A D X ) < U )
  assume ipcn.2: |- ( ph -> ( B D Y ) < T )


  assert |- ( ph -> ( abs ` ( ( A ., B ) - ( X ., Y ) ) ) < R )

  proof
    wph
    cA
    cB
    c.xi
    co
    #
    cX
    cY
    c.xi
    co
    #
    cA
    cY
    c.xi
    co
    #
    cR
    wph
    cW
    ccph
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    @0
    cc
    wcel
    ipcn.w
    ipcn.a
    ipcn.b
    cA
    cB
    c.xi
    cV
    cW
    ipcn.v
    ipcn.h
    cphipcl
    syl3anc
    #
    wph
    @3
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @1
    cc
    wcel
    ipcn.w
    ipcn.x
    ipcn.y
    cX
    cY
    c.xi
    cV
    cW
    ipcn.v
    ipcn.h
    cphipcl
    syl3anc
    #
    wph
    @3
    @4
    @8
    @2
    cc
    wcel
    ipcn.w
    ipcn.a
    ipcn.y
    cA
    cY
    c.xi
    cV
    cW
    ipcn.v
    ipcn.h
    cphipcl
    syl3anc
    #
    wph
    cR
    ipcn.r
    rpred
    #
    wph
    @0
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cN
    cfv
    #
    c1
    caddc
    co
    #
    cB
    cY
    cD
    co
    #
    cmul
    co
    #
    cR
    c2
    cdiv
    co
    #
    wph
    @12
    wph
    @0
    @2
    @6
    @10
    subcld
    abscld
    #
    wph
    @15
    @16
    wph
    @15
    wph
    @14
    wph
    cW
    cngp
    wcel
    #
    @4
    @14
    cr
    wcel
    wph
    cW
    cnlm
    wcel
    #
    @20
    wph
    @3
    @21
    ipcn.w
    cW
    cphnlm
    syl
    cW
    nlmngp
    syl
    #
    ipcn.a
    cA
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmcl
    syl2anc
    #
    wph
    @20
    @4
    cc0
    @14
    cle
    wbr
    @22
    ipcn.a
    cA
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmge0
    syl2anc
    ge0p1rpd
    #
    rpred
    #
    wph
    cW
    cmt
    wcel
    #
    @5
    @8
    @16
    cr
    wcel
    wph
    @20
    @26
    @22
    cW
    ngpms
    syl
    #
    ipcn.b
    ipcn.y
    cB
    cY
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    mscl
    syl3anc
    #
    remulcld
    #
    wph
    cR
    @11
    rehalfcld
    #
    wph
    @13
    @14
    @16
    cmul
    co
    #
    @17
    @19
    wph
    @14
    @16
    @23
    @28
    remulcld
    @29
    wph
    cA
    cB
    cY
    cW
    csg
    cfv
    #
    co
    #
    c.xi
    co
    #
    cabs
    cfv
    #
    @13
    @31
    cle
    wph
    @34
    @12
    cabs
    wph
    @3
    @4
    @5
    @8
    @34
    @12
    wceq
    ipcn.w
    ipcn.a
    ipcn.b
    ipcn.y
    cA
    cB
    cY
    c.xi
    @32
    cV
    cW
    ipcn.h
    ipcn.v
    @32
    eqid
    #
    cphsubdi
    syl13anc
    fveq2d
    wph
    @35
    @14
    @33
    cN
    cfv
    #
    cmul
    co
    #
    @31
    cle
    wph
    @3
    @4
    @33
    cV
    wcel
    #
    @35
    @38
    cle
    wbr
    ipcn.w
    ipcn.a
    wph
    cW
    cgrp
    wcel
    #
    @5
    @8
    @39
    wph
    @20
    @40
    @22
    cW
    ngpgrp
    syl
    #
    ipcn.b
    ipcn.y
    cV
    cW
    @32
    cB
    cY
    ipcn.v
    @36
    grpsubcl
    syl3anc
    c.xi
    cN
    cV
    cW
    cA
    @33
    ipcn.v
    ipcn.h
    ipcn.n
    ipcau
    syl3anc
    wph
    @16
    @37
    @14
    cmul
    wph
    @20
    @5
    @8
    @16
    @37
    wceq
    @22
    ipcn.b
    ipcn.y
    cB
    cY
    cD
    cW
    @32
    cN
    cV
    ipcn.n
    ipcn.v
    @36
    ipcn.d
    ngpds
    syl3anc
    oveq2d
    breqtrrd
    eqbrtrrd
    wph
    @14
    @15
    @16
    @23
    @25
    @28
    wph
    cW
    cxme
    wcel
    #
    @5
    @8
    cc0
    @16
    cle
    wbr
    wph
    @26
    @42
    @27
    cW
    msxms
    syl
    #
    ipcn.b
    ipcn.y
    cB
    cY
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    xmsge0
    syl3anc
    wph
    @14
    @23
    lep1d
    lemul1ad
    letrd
    wph
    @17
    @18
    clt
    wbr
    @16
    @18
    @15
    cdiv
    co
    #
    clt
    wbr
    wph
    @16
    cT
    @44
    clt
    ipcn.2
    ipcn.t
    syl6breq
    wph
    @16
    @18
    @15
    @28
    @30
    @24
    ltmuldiv2d
    mpbird
    lelttrd
    wph
    @2
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cX
    cD
    co
    #
    cB
    cN
    cfv
    #
    cT
    caddc
    co
    #
    cmul
    co
    #
    @18
    wph
    @45
    wph
    @2
    @1
    @10
    @9
    subcld
    abscld
    #
    wph
    @47
    @49
    wph
    @26
    @4
    @7
    @47
    cr
    wcel
    #
    @27
    ipcn.a
    ipcn.x
    cA
    cX
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    mscl
    syl3anc
    #
    wph
    @48
    cT
    wph
    @20
    @5
    @48
    cr
    wcel
    @22
    ipcn.b
    cB
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmcl
    syl2anc
    #
    wph
    cT
    wph
    cT
    @44
    crp
    ipcn.t
    wph
    @18
    @15
    wph
    cR
    ipcn.r
    rphalfcld
    @24
    rpdivcld
    syl5eqel
    #
    rpred
    #
    readdcld
    #
    remulcld
    #
    @30
    wph
    @46
    @47
    cY
    cN
    cfv
    #
    cmul
    co
    #
    @50
    @51
    wph
    @47
    @59
    @53
    wph
    @20
    @8
    @59
    cr
    wcel
    @22
    ipcn.y
    cY
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmcl
    syl2anc
    #
    remulcld
    @58
    wph
    cA
    cX
    @32
    co
    #
    cY
    c.xi
    co
    #
    cabs
    cfv
    #
    @46
    @60
    cle
    wph
    @63
    @45
    cabs
    wph
    @3
    @4
    @7
    @8
    @63
    @45
    wceq
    ipcn.w
    ipcn.a
    ipcn.x
    ipcn.y
    cA
    cX
    cY
    c.xi
    @32
    cV
    cW
    ipcn.h
    ipcn.v
    @36
    cphsubdir
    syl13anc
    fveq2d
    wph
    @64
    @62
    cN
    cfv
    #
    @59
    cmul
    co
    #
    @60
    cle
    wph
    @3
    @62
    cV
    wcel
    #
    @8
    @64
    @66
    cle
    wbr
    ipcn.w
    wph
    @40
    @4
    @7
    @67
    @41
    ipcn.a
    ipcn.x
    cV
    cW
    @32
    cA
    cX
    ipcn.v
    @36
    grpsubcl
    syl3anc
    ipcn.y
    c.xi
    cN
    cV
    cW
    @62
    cY
    ipcn.v
    ipcn.h
    ipcn.n
    ipcau
    syl3anc
    wph
    @47
    @65
    @59
    cmul
    wph
    @20
    @4
    @7
    @47
    @65
    wceq
    @22
    ipcn.a
    ipcn.x
    cA
    cX
    cD
    cW
    @32
    cN
    cV
    ipcn.n
    ipcn.v
    @36
    ipcn.d
    ngpds
    syl3anc
    oveq1d
    breqtrrd
    eqbrtrrd
    wph
    @59
    @49
    @47
    @61
    @57
    @53
    wph
    @42
    @4
    @7
    cc0
    @47
    cle
    wbr
    @43
    ipcn.a
    ipcn.x
    cA
    cX
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    xmsge0
    syl3anc
    wph
    @59
    @48
    cmin
    co
    #
    cT
    cle
    wbr
    @59
    @49
    cle
    wbr
    wph
    @68
    @16
    cT
    wph
    @59
    @48
    @61
    @54
    resubcld
    @28
    @56
    wph
    @68
    cY
    cB
    @32
    co
    cN
    cfv
    #
    @16
    cle
    wph
    @20
    @8
    @5
    @68
    @69
    cle
    wbr
    @22
    ipcn.y
    ipcn.b
    cY
    cB
    cW
    @32
    cN
    cV
    ipcn.v
    ipcn.n
    @36
    nm2dif
    syl3anc
    wph
    @20
    @5
    @8
    @16
    @69
    wceq
    @22
    ipcn.b
    ipcn.y
    cB
    cY
    cD
    cW
    @32
    cN
    cV
    ipcn.n
    ipcn.v
    @36
    ipcn.d
    ngpdsr
    syl3anc
    breqtrrd
    wph
    @16
    cT
    @28
    @56
    ipcn.2
    ltled
    letrd
    wph
    @59
    @48
    cT
    @61
    @54
    @56
    lesubadd2d
    mpbid
    lemul2ad
    letrd
    wph
    @50
    @18
    clt
    wbr
    #
    @47
    @18
    @49
    cdiv
    co
    #
    clt
    wbr
    #
    wph
    @47
    cU
    @71
    clt
    ipcn.1
    ipcn.u
    syl6breq
    wph
    @52
    @18
    cr
    wcel
    @49
    cr
    wcel
    cc0
    @49
    clt
    wbr
    @70
    @72
    wb
    @53
    @30
    @57
    wph
    cc0
    @48
    @49
    wph
    0red
    @54
    @57
    wph
    @20
    @5
    cc0
    @48
    cle
    wbr
    @22
    ipcn.b
    cB
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmge0
    syl2anc
    wph
    @48
    cT
    @54
    @55
    ltaddrpd
    lelttrd
    @47
    @18
    @49
    ltmuldiv
    syl112anc
    mpbird
    lelttrd
    abs3lemd
end
