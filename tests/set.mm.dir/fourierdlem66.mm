include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "c1.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "cr.mm"
include "wceq.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "eqimssi.mm"
include "difss.mm"
include "sstri.mm"
include "a1i.mm"
include "sselda.mm"
include "adantlr.mm"
include "wf.mm"
include "adantr.mm"
include "fourierdlem55.mm"
include "ffvelrnd.mm"
include "nnre.mm"
include "fourierdlem5.mm"
include "syl.mm"
include "ad2antlr.mm"
include "remulcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fourierdlem9.mm"
include "fourierdlem43.mm"
include "0red.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "sseldi.mm"
include "adantl.mm"
include "readdcld.mm"
include "ifcld.mm"
include "resubcld.mm"
include "simpr.mm"
include "eldifbd.mm"
include "velsn.mm"
include "sylnib.mm"
include "neqned.mm"
include "redivcld.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "1red.mm"
include "2re.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "2cnd.mm"
include "recnd.mm"
include "wne.mm"
include "2ne0.mm"
include "fourierdlem44.mm"
include "mulne0d.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "dmdcan2d.mm"
include "3eqtrd.mm"
include "cc.mm"
include "div32d.mm"
include "halfre.mm"
include "picn.mm"
include "rehalfcl.mm"
include "resincl.mm"
include "3syl.mm"
include "eldifsni.mm"
include "eleq2s.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "divdiv1d.mm"
include "mulassd.mm"
include "oveq2d.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "divcan2d.mm"
include "cmo.mm"
include "dirkerval2.mm"
include "sylan2.mm"
include "wn.mm"
include "fourierdlem24.mm"
include "neneqd.mm"
include "eqtr2d.mm"
include "3eqtr3d.mm"
include "adantll.mm"
include "dirkerre.mm"
include "mul12d.mm"

theorem fourierdlem66
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cS: class S
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem66.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem66.x: |- ( ph -> X e. RR )
  assume fourierdlem66.y: |- ( ph -> Y e. RR )
  assume fourierdlem66.w: |- ( ph -> W e. RR )
  assume fourierdlem66.d: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )
  assume fourierdlem66.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem66.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem66.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem66.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem66.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )
  assume fourierdlem66.a: |- A = ( ( -u _pi [,] _pi ) \ { 0 } )

  disjoint n s
  disjoint ph s
  disjoint k x
  assert |- ( ( ( ph /\ n e. NN ) /\ s e. A ) -> ( G ` s ) = ( _pi x. ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) x. ( ( D ` n ) ` s ) ) ) )

  proof
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    vs
    cv
    #
    cA
    wcel
    #
    wa
    #
    @3
    cG
    cfv
    #
    @3
    cU
    cfv
    #
    @3
    cS
    cfv
    #
    cmul
    co
    #
    cX
    @3
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    @3
    clt
    wbr
    #
    cY
    cW
    cif
    #
    cmin
    co
    #
    c2
    @3
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @0
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @3
    cmul
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cpi
    @14
    @3
    @0
    cD
    cfv
    cfv
    #
    cmul
    co
    cmul
    co
    #
    @5
    @3
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    #
    @9
    cr
    wcel
    @6
    @9
    wceq
    wph
    @4
    @28
    @1
    wph
    cA
    @27
    @3
    cA
    @27
    wss
    wph
    cA
    @27
    cc0
    csn
    #
    cdif
    #
    @27
    cA
    @30
    fourierdlem66.a
    eqimssi
    #
    @27
    @29
    difss
    sstri
    #
    a1i
    sselda
    #
    adantlr
    #
    @5
    @7
    @8
    @5
    @27
    cr
    @3
    cU
    @2
    @27
    cr
    cU
    wf
    @4
    @2
    cU
    cF
    cH
    cK
    cW
    cX
    cY
    vs
    wph
    cr
    cr
    cF
    wf
    #
    @1
    fourierdlem66.f
    adantr
    wph
    cX
    cr
    wcel
    #
    @1
    fourierdlem66.x
    adantr
    wph
    cY
    cr
    wcel
    @1
    fourierdlem66.y
    adantr
    wph
    cW
    cr
    wcel
    @1
    fourierdlem66.w
    adantr
    fourierdlem66.h
    fourierdlem66.k
    fourierdlem66.u
    fourierdlem55
    adantr
    @34
    ffvelrnd
    @5
    @27
    cr
    @3
    cS
    @1
    @27
    cr
    cS
    wf
    #
    wph
    @4
    @1
    @0
    cr
    wcel
    #
    @37
    @0
    nnre
    #
    vs
    cS
    @0
    fourierdlem66.s
    fourierdlem5
    syl
    ad2antlr
    @34
    ffvelrnd
    remulcld
    vs
    @27
    @9
    cr
    cG
    fourierdlem66.g
    fvmpt2
    syl2anc
    @5
    @7
    @18
    @8
    @22
    cmul
    wph
    @4
    @7
    @18
    wceq
    @1
    wph
    @4
    wa
    #
    @7
    @3
    cH
    cfv
    #
    @3
    cK
    cfv
    #
    cmul
    co
    #
    @14
    @3
    cdiv
    co
    #
    @3
    @17
    cdiv
    co
    #
    cmul
    co
    @18
    @40
    @28
    @43
    cr
    wcel
    @7
    @43
    wceq
    @33
    @40
    @41
    @42
    @40
    @27
    cr
    @3
    cH
    wph
    @27
    cr
    cH
    wf
    @4
    wph
    cF
    cH
    cW
    cX
    cY
    vs
    fourierdlem66.f
    fourierdlem66.x
    fourierdlem66.y
    fourierdlem66.w
    fourierdlem66.h
    fourierdlem9
    adantr
    @33
    ffvelrnd
    @40
    @27
    cr
    @3
    cK
    @27
    cr
    cK
    wf
    @40
    cK
    vs
    fourierdlem66.k
    fourierdlem43
    a1i
    @33
    ffvelrnd
    remulcld
    vs
    @27
    @43
    cr
    cU
    fourierdlem66.u
    fvmpt2
    syl2anc
    @40
    @41
    @44
    @42
    @45
    cmul
    @40
    @41
    @3
    cc0
    wceq
    #
    cc0
    @44
    cif
    #
    @44
    @40
    @28
    @47
    cr
    wcel
    @41
    @47
    wceq
    @33
    @40
    @46
    cc0
    @44
    cr
    @40
    0red
    @40
    @14
    @3
    @40
    @11
    @13
    @40
    cr
    cr
    @10
    cF
    wph
    @35
    @4
    fourierdlem66.f
    adantr
    @40
    cX
    @3
    wph
    @36
    @4
    fourierdlem66.x
    adantr
    @4
    @3
    cr
    wcel
    #
    wph
    @4
    @27
    cr
    @3
    @26
    cr
    wcel
    cpi
    cr
    wcel
    @27
    cr
    wss
    cpi
    pire
    renegcli
    pire
    @26
    cpi
    iccssre
    mp2an
    cA
    @27
    @3
    @32
    sseli
    #
    sseldi
    #
    adantl
    #
    readdcld
    ffvelrnd
    wph
    @13
    cr
    wcel
    @4
    wph
    @12
    cY
    cW
    cr
    fourierdlem66.y
    fourierdlem66.w
    ifcld
    adantr
    resubcld
    #
    @51
    @40
    @3
    cc0
    @40
    @3
    @29
    wcel
    @46
    @40
    @3
    @27
    @29
    @40
    cA
    @30
    @3
    @31
    wph
    @4
    simpr
    sseldi
    eldifbd
    vs
    cc0
    velsn
    sylnib
    #
    neqned
    #
    redivcld
    ifcld
    vs
    @27
    @47
    cr
    cH
    fourierdlem66.h
    fvmpt2
    syl2anc
    @40
    @46
    cc0
    @44
    @53
    iffalsed
    eqtrd
    @40
    @42
    @46
    c1
    @45
    cif
    #
    @45
    @40
    @28
    @55
    cr
    wcel
    @42
    @55
    wceq
    @33
    @40
    @46
    c1
    @45
    cr
    @40
    1red
    @40
    @3
    @17
    @51
    @40
    c2
    @16
    c2
    cr
    wcel
    #
    @40
    2re
    a1i
    @40
    @15
    @40
    @3
    @51
    rehalfcld
    resincld
    #
    remulcld
    @40
    c2
    @16
    @40
    2cnd
    #
    @40
    @16
    @57
    recnd
    #
    c2
    cc0
    wne
    #
    @40
    2ne0
    a1i
    @40
    @28
    @3
    cc0
    wne
    #
    @16
    cc0
    wne
    #
    @33
    @54
    @3
    fourierdlem44
    #
    syl2anc
    mulne0d
    #
    redivcld
    ifcld
    vs
    @27
    @55
    cr
    cK
    fourierdlem66.k
    fvmpt2
    syl2anc
    @40
    @46
    c1
    @45
    @53
    iffalsed
    eqtrd
    oveq12d
    @40
    @14
    @3
    @17
    @40
    @14
    @52
    recnd
    #
    @40
    @3
    @51
    recnd
    @40
    c2
    @16
    @58
    @59
    mulcld
    #
    @54
    @64
    dmdcan2d
    3eqtrd
    adantlr
    @5
    @28
    @22
    cr
    wcel
    @8
    @22
    wceq
    @34
    @5
    @21
    @5
    @20
    @3
    @5
    @0
    @19
    @1
    @38
    wph
    @4
    @39
    ad2antlr
    @5
    c1
    @5
    1red
    rehalfcld
    readdcld
    @4
    @48
    @2
    @50
    adantl
    remulcld
    resincld
    #
    vs
    @27
    @22
    cr
    cS
    fourierdlem66.s
    fvmpt2
    syl2anc
    oveq12d
    @5
    @23
    @14
    @22
    @17
    cdiv
    co
    #
    cmul
    co
    #
    @14
    cpi
    @24
    cmul
    co
    #
    cmul
    co
    #
    @25
    @5
    @14
    @17
    @22
    wph
    @4
    @14
    cc
    wcel
    @1
    @65
    adantlr
    #
    wph
    @4
    @17
    cc
    wcel
    @1
    @66
    adantlr
    @5
    @22
    @67
    recnd
    wph
    @4
    @17
    cc0
    wne
    #
    @1
    @64
    adantlr
    div32d
    @1
    @4
    @69
    @71
    wceq
    wph
    @1
    @4
    wa
    #
    @68
    @70
    @14
    cmul
    @74
    cpi
    @68
    cpi
    cdiv
    co
    #
    cmul
    co
    cpi
    @22
    c2
    cpi
    cmul
    co
    #
    @16
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    @68
    @70
    @74
    @75
    @78
    cpi
    cmul
    @74
    @75
    @22
    @17
    cpi
    cmul
    co
    #
    cdiv
    co
    @22
    c2
    @16
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cdiv
    co
    @78
    @74
    @22
    @17
    cpi
    @74
    @22
    @74
    @21
    @74
    @20
    @3
    @74
    @0
    @19
    @1
    @38
    @4
    @39
    adantr
    @19
    cr
    wcel
    @74
    halfre
    a1i
    readdcld
    @4
    @48
    @1
    @50
    adantl
    #
    remulcld
    resincld
    #
    recnd
    @74
    @17
    @74
    c2
    @16
    @56
    @74
    2re
    a1i
    @74
    @15
    @74
    @3
    @82
    rehalfcld
    resincld
    remulcld
    #
    recnd
    cpi
    cc
    wcel
    #
    @74
    picn
    a1i
    #
    @4
    @73
    @1
    @4
    c2
    @16
    @4
    2cnd
    @4
    @16
    @4
    @48
    @15
    cr
    wcel
    @16
    cr
    wcel
    @50
    @3
    rehalfcl
    @15
    resincl
    3syl
    recnd
    #
    @60
    @4
    2ne0
    a1i
    @4
    @28
    @61
    @62
    @49
    @61
    @3
    @30
    cA
    @3
    @27
    cc0
    eldifsni
    fourierdlem66.a
    eleq2s
    @63
    syl2anc
    mulne0d
    adantl
    #
    cpi
    cc0
    wne
    @74
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    #
    divdiv1d
    @74
    @79
    @81
    @22
    cdiv
    @74
    c2
    @16
    cpi
    @74
    2cnd
    #
    @4
    @16
    cc
    wcel
    @1
    @87
    adantl
    #
    @86
    mulassd
    oveq2d
    @74
    @81
    @77
    @22
    cdiv
    @74
    @81
    c2
    cpi
    @16
    cmul
    co
    #
    cmul
    co
    @77
    @74
    @80
    @92
    c2
    cmul
    @74
    @16
    cpi
    @91
    @86
    mulcomd
    oveq2d
    @74
    c2
    cpi
    @16
    @90
    @86
    @91
    mulassd
    eqtr4d
    oveq2d
    3eqtrd
    oveq2d
    @74
    @68
    cpi
    @74
    @68
    @74
    @22
    @17
    @83
    @84
    @88
    redivcld
    recnd
    @86
    @89
    divcan2d
    @74
    @78
    @24
    cpi
    cmul
    @74
    @24
    @3
    @76
    cmo
    co
    #
    cc0
    wceq
    #
    c2
    @0
    cmul
    co
    c1
    caddc
    co
    @76
    cdiv
    co
    #
    @78
    cif
    #
    @78
    @4
    @1
    @48
    @24
    @96
    wceq
    @50
    cD
    @3
    vn
    @0
    vs
    fourierdlem66.d
    dirkerval2
    sylan2
    @74
    @94
    @95
    @78
    @4
    @94
    wn
    @1
    @4
    @93
    cc0
    @93
    cc0
    wne
    @3
    @30
    cA
    @3
    fourierdlem24
    fourierdlem66.a
    eleq2s
    neneqd
    adantl
    iffalsed
    eqtr2d
    oveq2d
    3eqtr3d
    oveq2d
    adantll
    @5
    @14
    cpi
    @24
    @72
    @85
    @5
    picn
    a1i
    @1
    @4
    @24
    cc
    wcel
    wph
    @74
    @24
    @4
    @1
    @48
    @24
    cr
    wcel
    @50
    cD
    @3
    vn
    @0
    vs
    fourierdlem66.d
    dirkerre
    sylan2
    recnd
    adantll
    mul12d
    3eqtrd
    3eqtrd
end
