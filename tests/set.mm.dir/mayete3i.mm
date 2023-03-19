include "cin.mm"
include "chj.mm"
include "co.mm"
include "cph.mm"
include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "csm.mm"
include "chil.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "chjcli.mm"
include "cheli.mm"
include "eleq2s.mm"
include "adantr.mm"
include "sylbi.mm"
include "ax-hvmulid.mm"
include "cmul.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "recid2.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "halfcn.mm"
include "ax-hvmulass.mm"
include "mp3an12.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"
include "syl.mm"
include "cpjh.mm"
include "cfv.mm"
include "cva.mm"
include "cmv.mm"
include "hv2times.mm"
include "oveq1d.mm"
include "inss2.mm"
include "sseli.mm"
include "elin2.mm"
include "cort.mm"
include "wss.mm"
include "pjdsi.mm"
include "mpan2.mm"
include "oveqan12d.mm"
include "inss1.mm"
include "pjhcli.mm"
include "hvadd4.mm"
include "syl22anc.mm"
include "3syl.mm"
include "eqtrd.mm"
include "hvaddcl.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "syl6eleq.mm"
include "pjds3i.mm"
include "mpanr12.mm"
include "sylancl.mm"
include "oveq12d.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvpncan.mm"
include "mpancom.mm"
include "hvpncan2.mm"
include "pjcli.mm"
include "chshii.mm"
include "shsvai.mm"
include "shscli.mm"
include "eqeltrd.mm"
include "csh.mm"
include "shmulcl.mm"
include "ssriv.mm"
include "chsleji.mm"
include "shlessi.mm"
include "ax-mp.mm"
include "sstri.mm"
include "sseqtr4i.mm"

theorem mayete3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume mayete3.a: |- A e. CH
  assume mayete3.b: |- B e. CH
  assume mayete3.c: |- C e. CH
  assume mayete3.d: |- D e. CH
  assume mayete3.f: |- F e. CH
  assume mayete3.g: |- G e. CH
  assume mayete3.ac: |- A C_ ( _|_ ` C )
  assume mayete3.af: |- A C_ ( _|_ ` F )
  assume mayete3.cf: |- C C_ ( _|_ ` F )
  assume mayete3.ab: |- A C_ ( _|_ ` B )
  assume mayete3.cd: |- C C_ ( _|_ ` D )
  assume mayete3.fg: |- F C_ ( _|_ ` G )
  assume mayete3.x: |- X = ( ( A vH C ) vH F )
  assume mayete3.y: |- Y = ( ( ( A vH B ) i^i ( C vH D ) ) i^i ( F vH G ) )
  assume mayete3.z: |- Z = ( ( B vH D ) vH G )


  assert |- ( X i^i Y ) C_ Z

  proof
    cX
    cY
    cin
    #
    cB
    cD
    chj
    co
    #
    cG
    chj
    co
    #
    cZ
    @0
    @1
    cG
    cph
    co
    #
    @2
    @0
    cB
    cD
    cph
    co
    #
    cG
    cph
    co
    #
    @3
    vx
    @0
    @5
    vx
    cv
    #
    @0
    wcel
    #
    @6
    c1
    c2
    cdiv
    co
    #
    c2
    @6
    csm
    co
    #
    csm
    co
    #
    @5
    @7
    @6
    chil
    wcel
    #
    @6
    @10
    wceq
    @7
    @6
    cX
    wcel
    #
    @6
    cY
    wcel
    #
    wa
    @11
    @6
    cX
    cY
    elin
    @12
    @11
    @13
    @11
    @6
    cA
    cC
    chj
    co
    #
    cF
    chj
    co
    #
    cX
    @6
    @15
    @14
    cF
    cA
    cC
    mayete3.a
    mayete3.c
    chjcli
    mayete3.f
    chjcli
    cheli
    mayete3.x
    eleq2s
    adantr
    sylbi
    #
    @11
    c1
    @6
    csm
    co
    #
    @6
    @10
    @6
    ax-hvmulid
    @11
    @17
    @8
    c2
    cmul
    co
    #
    @6
    csm
    co
    #
    @10
    @18
    c1
    @6
    csm
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    @18
    c1
    wceq
    2cn
    2ne0
    c2
    recid2
    mp2an
    oveq1i
    @8
    cc
    wcel
    #
    @20
    @11
    @19
    @10
    wceq
    halfcn
    2cn
    @8
    c2
    @6
    ax-hvmulass
    mp3an12
    syl5eqr
    eqtr3d
    syl
    @7
    @9
    @5
    wcel
    #
    @10
    @5
    wcel
    #
    @7
    @9
    @6
    cB
    cpjh
    cfv
    cfv
    #
    @6
    cD
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    @6
    cG
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    @5
    @7
    @6
    cA
    cpjh
    cfv
    cfv
    #
    @6
    cC
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    @6
    cF
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    @28
    cva
    co
    #
    @33
    cmv
    co
    #
    @9
    @28
    @7
    @9
    @6
    cva
    co
    #
    @6
    cmv
    co
    #
    @35
    @9
    @7
    @36
    @34
    @6
    @33
    cmv
    @7
    @36
    @6
    @6
    cva
    co
    #
    @6
    cva
    co
    #
    @31
    @26
    cva
    co
    #
    @32
    @27
    cva
    co
    #
    cva
    co
    #
    @34
    @7
    @11
    @36
    @39
    wceq
    @16
    @11
    @9
    @38
    @6
    cva
    @6
    hv2times
    oveq1d
    syl
    @7
    @13
    @39
    @42
    wceq
    #
    @0
    cY
    @6
    cX
    cY
    inss2
    sseli
    @13
    @6
    cA
    cB
    chj
    co
    #
    cC
    cD
    chj
    co
    #
    cin
    #
    wcel
    #
    @6
    cF
    cG
    chj
    co
    #
    wcel
    #
    wa
    @43
    @6
    @46
    @48
    cY
    mayete3.y
    elin2
    @47
    @49
    @38
    @40
    @6
    @41
    cva
    @47
    @38
    @29
    @24
    cva
    co
    #
    @30
    @25
    cva
    co
    #
    cva
    co
    #
    @40
    @47
    @6
    @44
    wcel
    #
    @6
    @45
    wcel
    #
    wa
    @38
    @52
    wceq
    @6
    @44
    @45
    elin
    @53
    @54
    @6
    @50
    @6
    @51
    cva
    @53
    cA
    cB
    cort
    cfv
    wss
    @6
    @50
    wceq
    mayete3.ab
    @6
    cA
    cB
    mayete3.a
    mayete3.b
    pjdsi
    mpan2
    @54
    cC
    cD
    cort
    cfv
    wss
    @6
    @51
    wceq
    mayete3.cd
    @6
    cC
    cD
    mayete3.c
    mayete3.d
    pjdsi
    mpan2
    oveqan12d
    sylbi
    @47
    @53
    @11
    @52
    @40
    wceq
    #
    @46
    @44
    @6
    @44
    @45
    inss1
    sseli
    @6
    @44
    cA
    cB
    mayete3.a
    mayete3.b
    chjcli
    cheli
    @11
    @29
    chil
    wcel
    #
    @24
    chil
    wcel
    #
    @30
    chil
    wcel
    #
    @25
    chil
    wcel
    #
    @55
    @6
    cA
    mayete3.a
    pjhcli
    #
    @6
    cB
    mayete3.b
    pjhcli
    #
    @6
    cC
    mayete3.c
    pjhcli
    #
    @6
    cD
    mayete3.d
    pjhcli
    #
    @29
    @24
    @30
    @25
    hvadd4
    syl22anc
    3syl
    eqtrd
    @49
    cF
    cG
    cort
    cfv
    wss
    @6
    @41
    wceq
    mayete3.fg
    @6
    cF
    cG
    mayete3.f
    mayete3.g
    pjdsi
    mpan2
    oveqan12d
    sylbi
    syl
    @7
    @11
    @42
    @34
    wceq
    #
    @16
    @11
    @31
    chil
    wcel
    #
    @26
    chil
    wcel
    #
    @32
    chil
    wcel
    #
    @27
    chil
    wcel
    #
    @64
    @11
    @56
    @58
    @65
    @60
    @62
    @29
    @30
    hvaddcl
    syl2anc
    #
    @11
    @57
    @59
    @66
    @61
    @63
    @24
    @25
    hvaddcl
    syl2anc
    #
    @6
    cF
    mayete3.f
    pjhcli
    #
    @6
    cG
    mayete3.g
    pjhcli
    #
    @31
    @26
    @32
    @27
    hvadd4
    syl22anc
    syl
    3eqtrd
    @7
    @6
    @15
    wcel
    #
    cA
    cC
    cort
    cfv
    wss
    #
    @6
    @33
    wceq
    #
    @7
    @6
    cX
    @15
    @0
    cX
    @6
    cX
    cY
    inss1
    sseli
    mayete3.x
    syl6eleq
    mayete3.ac
    @73
    @74
    wa
    cA
    cF
    cort
    cfv
    #
    wss
    cC
    @76
    wss
    @75
    mayete3.af
    mayete3.cf
    @6
    cA
    cC
    cF
    mayete3.a
    mayete3.c
    mayete3.f
    pjds3i
    mpanr12
    sylancl
    oveq12d
    @7
    @11
    @37
    @9
    wceq
    #
    @16
    @9
    chil
    wcel
    #
    @11
    @77
    @20
    @11
    @78
    2cn
    c2
    @6
    hvmulcl
    mpan
    @9
    @6
    hvpncan
    mpancom
    syl
    eqtr3d
    @7
    @11
    @35
    @28
    wceq
    #
    @16
    @11
    @33
    chil
    wcel
    #
    @28
    chil
    wcel
    #
    @79
    @11
    @65
    @67
    @80
    @69
    @71
    @31
    @32
    hvaddcl
    syl2anc
    @11
    @66
    @68
    @81
    @70
    @72
    @26
    @27
    hvaddcl
    syl2anc
    @33
    @28
    hvpncan2
    syl2anc
    syl
    eqtr3d
    @7
    @11
    @28
    @5
    wcel
    #
    @16
    @11
    @26
    @4
    wcel
    #
    @27
    cG
    wcel
    @82
    @11
    @24
    cB
    wcel
    @25
    cD
    wcel
    @83
    @6
    cB
    mayete3.b
    pjcli
    @6
    cD
    mayete3.d
    pjcli
    cB
    cD
    @24
    @25
    cB
    mayete3.b
    chshii
    #
    cD
    mayete3.d
    chshii
    #
    shsvai
    syl2anc
    @6
    cG
    mayete3.g
    pjcli
    @4
    cG
    @26
    @27
    cB
    cD
    @84
    @85
    shscli
    #
    cG
    mayete3.g
    chshii
    #
    shsvai
    syl2anc
    syl
    eqeltrd
    @5
    csh
    wcel
    @21
    @22
    @23
    @4
    cG
    @86
    @87
    shscli
    halfcn
    @8
    @9
    @5
    shmulcl
    mp3an12
    syl
    eqeltrd
    ssriv
    @4
    @1
    wss
    @5
    @3
    wss
    cB
    cD
    mayete3.b
    mayete3.d
    chsleji
    @4
    @1
    cG
    @86
    @1
    cB
    cD
    mayete3.b
    mayete3.d
    chjcli
    #
    chshii
    @87
    shlessi
    ax-mp
    sstri
    @1
    cG
    @88
    mayete3.g
    chsleji
    sstri
    mayete3.z
    sseqtr4i
end
