include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "cmul.mm"
include "cmpt.mm"
include "climc.mm"
include "cres.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "eqid.mm"
include "cc.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "cxr.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "a1i.mm"
include "cfz.mm"
include "wf.mm"
include "cr.mm"
include "renegcld.mm"
include "crn.mm"
include "cmap.mm"
include "wss.mm"
include "wral.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "frn.mm"
include "3syl.mm"
include "sseldd.mm"
include "fourierdlem14.mm"
include "fourierdlem15.mm"
include "adantr.mm"
include "simplr.mm"
include "fourierdlem8.mm"
include "ioossicc.mm"
include "sseli.mm"
include "adantl.mm"
include "cpnf.mm"
include "ioossre.mm"
include "fssresd.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "lptioo1cn.mm"
include "limcrecl.mm"
include "fourierdlem9.mm"
include "fssd.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "fourierdlem43.mm"
include "recnd.mm"
include "mulcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ccncf.mm"
include "fourierdlem18.mm"
include "cncff.mm"
include "fourierdlem75.mm"
include "simpr.mm"
include "syl5ss.mm"
include "feqresmpt.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "limcresi.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "fourierdlem62.mm"
include "sselii.mm"
include "elfzofz.mm"
include "cnlimci.mm"
include "sseldi.mm"
include "mp1i.mm"
include "mullimc.mm"
include "mpteq2dva.mm"
include "eleqtrrd.mm"
include "syl5eqel.mm"
include "reseq1i.mm"
include "resmptd.mm"
include "syl5req.mm"

theorem fourierdlem85
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem85.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( -u _pi + X ) /\ ( p ` m ) = ( _pi + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem85.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem85.x: |- ( ph -> X e. ran V )
  assume fourierdlem85.y: |- ( ph -> Y e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem85.w: |- ( ph -> W e. RR )
  assume fourierdlem85.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem85.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem85.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem85.n: |- ( ph -> N e. RR )
  assume fourierdlem85.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem85.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )
  assume fourierdlem85.m: |- ( ph -> M e. NN )
  assume fourierdlem85.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem85.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` i ) ) )
  assume fourierdlem85.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )
  assume fourierdlem85.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = -u _pi /\ ( p ` m ) = _pi ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem85.i: |- I = ( RR _D F )
  assume fourierdlem85.ifn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( I |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) : ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) --> CC )
  assume fourierdlem85.e: |- ( ph -> E e. ( ( I |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem85.a: |- A = ( ( if ( ( V ` i ) = X , E , ( ( R - if ( ( V ` i ) < X , W , Y ) ) / ( Q ` i ) ) ) x. ( K ` ( Q ` i ) ) ) x. ( S ` ( Q ` i ) ) )

  disjoint E s
  disjoint F s
  disjoint H s
  disjoint K s
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint M s
  disjoint i s
  disjoint N s
  disjoint Q i
  disjoint Q p
  disjoint Q s
  disjoint R s
  disjoint S s
  disjoint V i
  disjoint V p
  disjoint V s
  disjoint W s
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X s
  disjoint Y s
  disjoint i ph
  disjoint ph s
  disjoint k x
  assert |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> A e. ( ( G |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )

  proof
    wph
    vi
    cv
    #
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cA
    vs
    @0
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    vs
    cv
    #
    cU
    cfv
    #
    @8
    cS
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @4
    climc
    co
    #
    cG
    @7
    cres
    #
    @4
    climc
    co
    @3
    cA
    @0
    cV
    cfv
    #
    cX
    wceq
    cE
    cR
    @15
    cX
    clt
    wbr
    cW
    cY
    cif
    cmin
    co
    @4
    cdiv
    co
    cif
    #
    @4
    cK
    cfv
    #
    cmul
    co
    #
    @4
    cS
    cfv
    #
    cmul
    co
    @13
    fourierdlem85.a
    @3
    vs
    @7
    @9
    @10
    @4
    vs
    @7
    @9
    cmpt
    #
    vs
    @7
    @10
    cmpt
    #
    @12
    @18
    @19
    @20
    eqid
    @21
    eqid
    @12
    eqid
    @3
    @8
    @7
    wcel
    #
    wa
    #
    @9
    @8
    cH
    cfv
    #
    @8
    cK
    cfv
    #
    cmul
    co
    #
    cc
    @23
    @8
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    @26
    cc
    wcel
    @9
    @26
    wceq
    @23
    @4
    @6
    cicc
    co
    #
    @28
    @8
    @23
    @27
    cpi
    cQ
    @0
    cM
    @27
    cxr
    wcel
    #
    @23
    @27
    cpi
    pire
    renegcli
    rexri
    #
    a1i
    cpi
    cxr
    wcel
    #
    @23
    cpi
    pire
    rexri
    #
    a1i
    @3
    cc0
    cM
    cfz
    co
    #
    @28
    cQ
    wf
    #
    @22
    wph
    @35
    @2
    wph
    @27
    cpi
    cO
    cQ
    vi
    vm
    cM
    vp
    fourierdlem85.o
    fourierdlem85.m
    wph
    @27
    cpi
    cP
    cQ
    vi
    vm
    cM
    cO
    cV
    cX
    vp
    wph
    cpi
    cpi
    cr
    wcel
    wph
    pire
    a1i
    #
    renegcld
    @36
    wph
    cV
    crn
    #
    cr
    cX
    wph
    cV
    cr
    @34
    cmap
    co
    wcel
    #
    @34
    cr
    cV
    wf
    @37
    cr
    wss
    wph
    @38
    cc0
    cV
    cfv
    @27
    cX
    caddc
    co
    #
    wceq
    cM
    cV
    cfv
    cpi
    cX
    caddc
    co
    #
    wceq
    wa
    @15
    @5
    cV
    cfv
    clt
    wbr
    vi
    @1
    wral
    wa
    #
    wph
    cV
    cM
    cP
    cfv
    wcel
    #
    @38
    @41
    wa
    #
    fourierdlem85.v
    wph
    cM
    cn
    wcel
    @42
    @43
    wb
    fourierdlem85.m
    @39
    @40
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem85.p
    fourierdlem2
    syl
    mpbid
    simpld
    cV
    cr
    @34
    elmapi
    @34
    cr
    cV
    frn
    3syl
    fourierdlem85.x
    sseldd
    #
    fourierdlem85.p
    fourierdlem85.o
    fourierdlem85.m
    fourierdlem85.v
    fourierdlem85.q
    fourierdlem14
    fourierdlem15
    adantr
    #
    adantr
    wph
    @2
    @22
    simplr
    fourierdlem8
    @22
    @8
    @29
    wcel
    @3
    @7
    @29
    @8
    @4
    @6
    ioossicc
    #
    sseli
    adantl
    sseldd
    #
    @23
    @24
    @25
    @23
    @28
    cc
    @8
    cH
    wph
    @28
    cc
    cH
    wf
    @2
    @22
    wph
    @28
    cr
    cc
    cH
    wph
    cF
    cH
    cW
    cX
    cY
    vs
    fourierdlem85.f
    @44
    wph
    cX
    cpnf
    cioo
    co
    #
    cX
    cF
    @48
    cres
    cY
    wph
    cr
    cr
    @48
    cF
    fourierdlem85.f
    @48
    cr
    wss
    wph
    cX
    cpnf
    ioossre
    a1i
    #
    fssresd
    wph
    @48
    cr
    cc
    @49
    ax-resscn
    syl6ss
    wph
    cX
    cpnf
    ccnfld
    ctopn
    cfv
    #
    @50
    eqid
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    @44
    wph
    cX
    @44
    ltpnfd
    lptioo1cn
    fourierdlem85.y
    limcrecl
    fourierdlem85.w
    fourierdlem85.h
    fourierdlem9
    #
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    fssd
    ad2antrr
    @47
    ffvelrnd
    #
    @23
    @25
    @23
    @28
    cr
    @8
    cK
    @28
    cr
    cK
    wf
    @23
    cK
    vs
    fourierdlem85.k
    fourierdlem43
    a1i
    @47
    ffvelrnd
    recnd
    #
    mulcld
    #
    vs
    @28
    @26
    cc
    cU
    fourierdlem85.u
    fvmpt2
    syl2anc
    #
    @55
    eqeltrd
    @23
    @10
    @23
    @28
    cr
    @8
    cS
    @3
    @28
    cr
    cS
    wf
    #
    @22
    wph
    @57
    @2
    wph
    cS
    @28
    cr
    ccncf
    co
    #
    wcel
    #
    @57
    wph
    cS
    cN
    vs
    fourierdlem85.n
    fourierdlem85.s
    fourierdlem18
    #
    @28
    cr
    cS
    cncff
    syl
    adantr
    #
    adantr
    @47
    ffvelrnd
    recnd
    @3
    @18
    vs
    @7
    @26
    cmpt
    #
    @4
    climc
    co
    @20
    @4
    climc
    co
    @3
    vs
    @7
    @24
    @25
    @4
    vs
    @7
    @24
    cmpt
    #
    vs
    @7
    @25
    cmpt
    #
    @62
    @16
    @17
    @63
    eqid
    @64
    eqid
    @62
    eqid
    @53
    @54
    @3
    @16
    cH
    @7
    cres
    #
    @4
    climc
    co
    @63
    @4
    climc
    co
    wph
    @16
    cP
    cQ
    cR
    vi
    vm
    cE
    cF
    cI
    cH
    cM
    cO
    cV
    cW
    cX
    cY
    vs
    vp
    @44
    fourierdlem85.p
    fourierdlem85.f
    fourierdlem85.x
    fourierdlem85.y
    fourierdlem85.w
    fourierdlem85.h
    fourierdlem85.m
    fourierdlem85.v
    fourierdlem85.r
    fourierdlem85.q
    fourierdlem85.o
    fourierdlem85.i
    fourierdlem85.ifn
    fourierdlem85.e
    @16
    eqid
    fourierdlem75
    @3
    @65
    @63
    @4
    climc
    @3
    vs
    @28
    cr
    @7
    cH
    wph
    @28
    cr
    cH
    wf
    @2
    @51
    adantr
    @3
    @7
    @29
    @28
    @46
    @3
    @27
    cpi
    cQ
    @0
    cM
    @30
    @3
    @31
    a1i
    @32
    @3
    @33
    a1i
    @45
    wph
    @2
    simpr
    fourierdlem8
    syl5ss
    #
    feqresmpt
    oveq1d
    eleqtrd
    @3
    @17
    cK
    @7
    cres
    #
    @4
    climc
    co
    #
    @64
    @4
    climc
    co
    @3
    cK
    @4
    climc
    co
    @68
    @17
    @4
    @7
    cK
    limcresi
    @3
    @28
    @4
    cc
    cK
    cK
    @28
    cc
    ccncf
    co
    #
    wcel
    #
    @3
    @58
    @69
    cK
    @52
    cc
    cc
    wss
    @58
    @69
    wss
    ax-resscn
    cc
    ssid
    @28
    cr
    cc
    cncfss
    mp2an
    vs
    cK
    fourierdlem85.k
    fourierdlem62
    sselii
    #
    a1i
    @3
    @34
    @28
    @0
    cQ
    @45
    @2
    @0
    @34
    wcel
    wph
    @0
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    #
    cnlimci
    sseldi
    @3
    @67
    @64
    @4
    climc
    @3
    vs
    @28
    cc
    @7
    cK
    @70
    @28
    cc
    cK
    wf
    @3
    @71
    @28
    cc
    cK
    cncff
    mp1i
    @66
    feqresmpt
    oveq1d
    eleqtrd
    mullimc
    @3
    @20
    @62
    @4
    climc
    @3
    vs
    @7
    @9
    @26
    @56
    mpteq2dva
    oveq1d
    eleqtrrd
    @3
    @19
    cS
    @7
    cres
    #
    @4
    climc
    co
    #
    @21
    @4
    climc
    co
    @3
    cS
    @4
    climc
    co
    @74
    @19
    @4
    @7
    cS
    limcresi
    @3
    @28
    @4
    cr
    cS
    wph
    @59
    @2
    @60
    adantr
    @72
    cnlimci
    sseldi
    @3
    @73
    @21
    @4
    climc
    @3
    vs
    @28
    cr
    @7
    cS
    @61
    @66
    feqresmpt
    oveq1d
    eleqtrd
    mullimc
    syl5eqel
    @3
    @12
    @14
    @4
    climc
    @3
    @14
    vs
    @28
    @11
    cmpt
    #
    @7
    cres
    @12
    cG
    @75
    @7
    fourierdlem85.g
    reseq1i
    @3
    vs
    @28
    @7
    @11
    @66
    resmptd
    syl5req
    oveq1d
    eleqtrd
end
