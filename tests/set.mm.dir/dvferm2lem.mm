include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cdiv.mm"
include "cr.mm"
include "cdv.mm"
include "caddc.mm"
include "cabs.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cioo.mm"
include "cxr.mm"
include "cle.mm"
include "wss.mm"
include "c0.mm"
include "ne0i.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "3syl.mm"
include "simprd.mm"
include "eliooord.mm"
include "syl.mm"
include "ioossre.mm"
include "sseldi.mm"
include "rexrd.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "iooss2.mm"
include "sstrd.mm"
include "cif.mm"
include "c2.mm"
include "cmnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rpred.mm"
include "resubcld.mm"
include "simpld.mm"
include "ifcld.mm"
include "mnflt.mm"
include "xrmax2.mm"
include "xrltletrd.mm"
include "ltsubrpd.mm"
include "breq1.mm"
include "ifboth.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "syl5eqel.mm"
include "xrmax1.mm"
include "wb.mm"
include "avglt1.mm"
include "mpbid.mm"
include "syl6breqr.mm"
include "xrlelttrd.mm"
include "avglt2.mm"
include "syl5eqbr.mm"
include "w3a.mm"
include "elioo2.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "ltned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ltled.mm"
include "abssuble0d.mm"
include "lelttrd.mm"
include "ltsub23d.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "wceq.mm"
include "neeq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "subne0d.mm"
include "redivcld.mm"
include "cdm.mm"
include "wf.mm"
include "dvfre.mm"
include "renegcld.mm"
include "absdifltd.mm"
include "negidd.mm"
include "breqtrd.mm"
include "lt0neg1d.mm"
include "divneg2d.mm"
include "posdifd.mm"
include "negsubdi2d.mm"
include "breqtrrd.mm"
include "gt0div.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wn.mm"
include "sylc.mm"
include "lenltd.mm"
include "pm2.65i.mm"

theorem dvferm2lem
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  assume dvferm.a: |- ( ph -> F : X --> RR )
  assume dvferm.b: |- ( ph -> X C_ RR )
  assume dvferm.u: |- ( ph -> U e. ( A (,) B ) )
  assume dvferm.s: |- ( ph -> ( A (,) B ) C_ X )
  assume dvferm.d: |- ( ph -> U e. dom ( RR _D F ) )
  assume dvferm2.r: |- ( ph -> A. y e. ( A (,) U ) ( F ` y ) <_ ( F ` U ) )
  assume dvferm2.z: |- ( ph -> ( ( RR _D F ) ` U ) < 0 )
  assume dvferm2.t: |- ( ph -> T e. RR+ )
  assume dvferm2.l: |- ( ph -> A. z e. ( X \ { U } ) ( ( z =/= U /\ ( abs ` ( z - U ) ) < T ) -> ( abs ` ( ( ( ( F ` z ) - ( F ` U ) ) / ( z - U ) ) - ( ( RR _D F ) ` U ) ) ) < -u ( ( RR _D F ) ` U ) ) )
  assume dvferm2.x: |- S = ( ( if ( A <_ ( U - T ) , ( U - T ) , A ) + U ) / 2 )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint U y
  disjoint U z
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint S y
  disjoint S z
  disjoint T z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint U u
  disjoint U x
  disjoint X u
  disjoint X x
  disjoint ph u
  assert |- -. ph

  proof
    wph
    cU
    cF
    cfv
    #
    cS
    cF
    cfv
    #
    clt
    wbr
    #
    wph
    @2
    cc0
    @1
    @0
    cmin
    co
    #
    clt
    wbr
    #
    wph
    @4
    cc0
    @3
    cS
    cU
    cmin
    co
    #
    cneg
    #
    cdiv
    co
    #
    clt
    wbr
    #
    wph
    cc0
    @3
    @5
    cdiv
    co
    #
    cneg
    #
    @7
    clt
    wph
    @9
    cc0
    clt
    wbr
    cc0
    @10
    clt
    wbr
    wph
    @9
    cU
    cr
    cF
    cdv
    co
    #
    cfv
    #
    @12
    cneg
    #
    caddc
    co
    #
    cc0
    clt
    wph
    @12
    @13
    cmin
    co
    @9
    clt
    wbr
    #
    @9
    @14
    clt
    wbr
    #
    wph
    @9
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    @15
    @16
    wa
    wph
    cS
    cX
    cU
    csn
    cdif
    #
    wcel
    #
    vz
    cv
    #
    cU
    wne
    #
    @22
    cU
    cmin
    co
    #
    cabs
    cfv
    #
    cT
    clt
    wbr
    #
    wa
    #
    @22
    cF
    cfv
    #
    @0
    cmin
    co
    #
    @24
    cdiv
    co
    #
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vz
    @20
    wral
    cS
    cU
    wne
    #
    @5
    cabs
    cfv
    #
    cT
    clt
    wbr
    #
    wa
    #
    @19
    wph
    cS
    cX
    wcel
    @35
    @21
    wph
    cA
    cU
    cioo
    co
    #
    cX
    cS
    wph
    @39
    cA
    cB
    cioo
    co
    #
    cX
    wph
    cB
    cxr
    wcel
    #
    cU
    cB
    cle
    wbr
    #
    @39
    @40
    wss
    wph
    cA
    cxr
    wcel
    #
    @41
    wph
    cU
    @40
    wcel
    #
    @40
    c0
    wne
    @43
    @41
    wa
    #
    dvferm.u
    @40
    cU
    ne0i
    @45
    @40
    c0
    cA
    cB
    ndmioo
    necon1ai
    3syl
    #
    simprd
    #
    wph
    cU
    cB
    clt
    wbr
    #
    @42
    wph
    cA
    cU
    clt
    wbr
    #
    @48
    wph
    @44
    @49
    @48
    wa
    dvferm.u
    cU
    cA
    cB
    eliooord
    syl
    #
    simprd
    wph
    cU
    cxr
    wcel
    #
    @41
    @48
    @42
    wi
    wph
    cU
    wph
    @40
    cr
    cU
    cA
    cB
    ioossre
    dvferm.u
    sseldi
    #
    rexrd
    #
    @47
    cU
    cB
    xrltle
    syl2anc
    mpd
    cA
    cU
    cB
    iooss2
    syl2anc
    dvferm.s
    sstrd
    wph
    cS
    @39
    wcel
    #
    cS
    cr
    wcel
    #
    cA
    cS
    clt
    wbr
    #
    cS
    cU
    clt
    wbr
    #
    wph
    cS
    cA
    cU
    cT
    cmin
    co
    #
    cle
    wbr
    #
    @58
    cA
    cif
    #
    cU
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cr
    dvferm2.x
    wph
    @61
    wph
    @60
    cU
    wph
    cmnf
    cxr
    wcel
    #
    @60
    cxr
    wcel
    @51
    cmnf
    @60
    clt
    wbr
    @60
    cU
    clt
    wbr
    #
    @60
    cr
    wcel
    #
    @63
    wph
    mnfxr
    a1i
    #
    wph
    @59
    @58
    cA
    cxr
    wph
    @58
    wph
    cU
    cT
    @52
    wph
    cT
    dvferm2.t
    rpred
    #
    resubcld
    #
    rexrd
    #
    wph
    @43
    @41
    @46
    simpld
    #
    ifcld
    #
    @53
    wph
    cmnf
    @58
    @60
    @66
    @69
    @71
    wph
    @58
    cr
    wcel
    cmnf
    @58
    clt
    wbr
    @68
    @58
    mnflt
    syl
    wph
    @43
    @58
    cxr
    wcel
    #
    @58
    @60
    cle
    wbr
    @70
    @69
    cA
    @58
    xrmax2
    syl2anc
    #
    xrltletrd
    wph
    @58
    cU
    clt
    wbr
    #
    @49
    @64
    wph
    cU
    cT
    @52
    dvferm2.t
    ltsubrpd
    wph
    @49
    @48
    @50
    simpld
    @59
    @74
    @49
    @64
    @58
    cA
    @58
    @60
    cU
    clt
    breq1
    cA
    @60
    cU
    clt
    breq1
    ifboth
    syl2anc
    #
    cmnf
    @60
    cU
    xrre2
    syl32anc
    #
    @52
    readdcld
    rehalfcld
    syl5eqel
    #
    wph
    cA
    @60
    cS
    @70
    @71
    wph
    cS
    @77
    rexrd
    wph
    @43
    @72
    cA
    @60
    cle
    wbr
    @70
    @69
    cA
    @58
    xrmax1
    syl2anc
    wph
    @60
    @62
    cS
    clt
    wph
    @64
    @60
    @62
    clt
    wbr
    #
    @75
    wph
    @65
    cU
    cr
    wcel
    #
    @64
    @78
    wb
    @76
    @52
    @60
    cU
    avglt1
    syl2anc
    mpbid
    dvferm2.x
    syl6breqr
    #
    xrlelttrd
    wph
    cS
    @62
    cU
    clt
    dvferm2.x
    wph
    @64
    @62
    cU
    clt
    wbr
    #
    @75
    wph
    @65
    @79
    @64
    @81
    wb
    @76
    @52
    @60
    cU
    avglt2
    syl2anc
    mpbid
    syl5eqbr
    #
    wph
    @43
    @51
    @54
    @55
    @56
    @57
    w3a
    wb
    @70
    @53
    cA
    cU
    cS
    elioo2
    syl2anc
    mpbir3and
    #
    sseldd
    #
    wph
    cS
    cU
    @77
    @82
    ltned
    #
    cS
    cX
    cU
    eldifsn
    sylanbrc
    dvferm2.l
    wph
    @35
    @37
    @85
    wph
    @36
    cU
    cS
    cmin
    co
    #
    cT
    clt
    wph
    cS
    cU
    @77
    @52
    wph
    cS
    cU
    @77
    @52
    @82
    ltled
    abssuble0d
    wph
    cU
    cT
    cS
    @52
    @67
    @77
    wph
    @58
    @60
    cS
    @68
    @76
    @77
    @73
    @80
    lelttrd
    ltsub23d
    eqbrtrd
    jca
    @34
    @38
    @19
    wi
    vz
    cS
    @20
    @22
    cS
    wceq
    #
    @27
    @38
    @33
    @19
    @87
    @23
    @35
    @26
    @37
    @22
    cS
    cU
    neeq1
    @87
    @25
    @36
    cT
    clt
    @87
    @24
    @5
    cabs
    @22
    cS
    cU
    cmin
    oveq1
    #
    fveq2d
    breq1d
    anbi12d
    @87
    @32
    @18
    @13
    clt
    @87
    @31
    @17
    cabs
    @87
    @30
    @9
    @12
    cmin
    @87
    @29
    @3
    @24
    @5
    cdiv
    @87
    @28
    @1
    @0
    cmin
    @22
    cS
    cF
    fveq2
    oveq1d
    @88
    oveq12d
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl3c
    wph
    @9
    @12
    @13
    wph
    @3
    @5
    wph
    @1
    @0
    wph
    cX
    cr
    cS
    cF
    dvferm.a
    @84
    ffvelrnd
    #
    wph
    cX
    cr
    cU
    cF
    dvferm.a
    wph
    @40
    cX
    cU
    dvferm.s
    dvferm.u
    sseldd
    ffvelrnd
    #
    resubcld
    #
    wph
    cS
    cU
    @77
    @52
    resubcld
    #
    wph
    cS
    cU
    wph
    cS
    @77
    recnd
    #
    wph
    cU
    @52
    recnd
    #
    @85
    subne0d
    #
    redivcld
    #
    wph
    @11
    cdm
    #
    cr
    cU
    @11
    wph
    cX
    cr
    cF
    wf
    cX
    cr
    wss
    @97
    cr
    @11
    wf
    dvferm.a
    dvferm.b
    cX
    cF
    dvfre
    syl2anc
    dvferm.d
    ffvelrnd
    #
    wph
    @12
    @98
    renegcld
    absdifltd
    mpbid
    simprd
    wph
    @12
    wph
    @12
    @98
    recnd
    negidd
    breqtrd
    wph
    @9
    @96
    lt0neg1d
    mpbid
    wph
    @3
    @5
    wph
    @3
    @91
    recnd
    wph
    @5
    @92
    recnd
    @95
    divneg2d
    breqtrd
    wph
    @3
    cr
    wcel
    @6
    cr
    wcel
    cc0
    @6
    clt
    wbr
    @4
    @8
    wb
    @91
    wph
    @5
    @92
    renegcld
    wph
    cc0
    @86
    @6
    clt
    wph
    @57
    cc0
    @86
    clt
    wbr
    @82
    wph
    cS
    cU
    @77
    @52
    posdifd
    mpbid
    wph
    cS
    cU
    @93
    @94
    negsubdi2d
    breqtrrd
    @3
    @6
    gt0div
    syl3anc
    mpbird
    wph
    @0
    @1
    @90
    @89
    posdifd
    mpbird
    wph
    @1
    @0
    cle
    wbr
    #
    @2
    wn
    wph
    @54
    vy
    cv
    #
    cF
    cfv
    #
    @0
    cle
    wbr
    #
    vy
    @39
    wral
    @99
    @83
    dvferm2.r
    @102
    @99
    vy
    cS
    @39
    @100
    cS
    wceq
    @101
    @1
    @0
    cle
    @100
    cS
    cF
    fveq2
    breq1d
    rspcv
    sylc
    wph
    @1
    @0
    @89
    @90
    lenltd
    mpbid
    pm2.65i
end
