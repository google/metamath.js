include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cr.mm"
include "cdv.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "subidd.mm"
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
include "c0.mm"
include "ne0i.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "3syl.mm"
include "simpld.mm"
include "eliooord.mm"
include "syl.mm"
include "ioossre.mm"
include "sseldi.mm"
include "rexrd.mm"
include "xrltle.mm"
include "mpd.mm"
include "iooss1.mm"
include "sstrd.mm"
include "cif.mm"
include "c2.mm"
include "cmnf.mm"
include "simprd.mm"
include "rpred.mm"
include "readdcld.mm"
include "ifcld.mm"
include "mnfxr.mm"
include "a1i.mm"
include "mnflt.mm"
include "xrlttrd.mm"
include "breq2.mm"
include "ifboth.mm"
include "xrmin2.mm"
include "xrre.mm"
include "syl22anc.mm"
include "rehalfcld.mm"
include "syl5eqel.mm"
include "ltaddrpd.mm"
include "wb.mm"
include "avglt1.mm"
include "mpbid.mm"
include "syl6breqr.mm"
include "avglt2.mm"
include "syl5eqbr.mm"
include "xrmin1.mm"
include "xrltletrd.mm"
include "w3a.mm"
include "elioo2.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "gtned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ltled.mm"
include "abssubge0d.mm"
include "ltletrd.mm"
include "ltsubadd2d.mm"
include "mpbird.mm"
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
include "resubcld.mm"
include "posdifd.mm"
include "elrpd.mm"
include "rerpdivcld.mm"
include "absdifltd.mm"
include "eqbrtrrd.mm"
include "gt0div.mm"
include "syl3anc.mm"
include "wn.mm"
include "sylc.mm"
include "lenltd.mm"
include "pm2.65i.mm"

theorem dvferm1lem
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
  assume dvferm1.r: |- ( ph -> A. y e. ( U (,) B ) ( F ` y ) <_ ( F ` U ) )
  assume dvferm1.z: |- ( ph -> 0 < ( ( RR _D F ) ` U ) )
  assume dvferm1.t: |- ( ph -> T e. RR+ )
  assume dvferm1.l: |- ( ph -> A. z e. ( X \ { U } ) ( ( z =/= U /\ ( abs ` ( z - U ) ) < T ) -> ( abs ` ( ( ( ( F ` z ) - ( F ` U ) ) / ( z - U ) ) - ( ( RR _D F ) ` U ) ) ) < ( ( RR _D F ) ` U ) ) )
  assume dvferm1.x: |- S = ( ( U + if ( B <_ ( U + T ) , B , ( U + T ) ) ) / 2 )

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
    cdiv
    co
    #
    clt
    wbr
    #
    wph
    cU
    cr
    cF
    cdv
    co
    #
    cfv
    #
    @9
    cmin
    co
    #
    cc0
    @6
    clt
    wph
    @9
    wph
    @9
    wph
    @8
    cdm
    #
    cr
    cU
    @8
    wph
    cX
    cr
    cF
    wf
    cX
    cr
    wss
    @11
    cr
    @8
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
    recnd
    subidd
    wph
    @10
    @6
    clt
    wbr
    #
    @6
    @9
    @9
    caddc
    co
    clt
    wbr
    #
    wph
    @6
    @9
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    @13
    @14
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
    @20
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
    @20
    cF
    cfv
    #
    @0
    cmin
    co
    #
    @22
    cdiv
    co
    #
    @9
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    wi
    #
    vz
    @18
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
    @17
    wph
    cS
    cX
    wcel
    @33
    @19
    wph
    cU
    cB
    cioo
    co
    #
    cX
    cS
    wph
    @37
    cA
    cB
    cioo
    co
    #
    cX
    wph
    cA
    cxr
    wcel
    #
    cA
    cU
    cle
    wbr
    #
    @37
    @38
    wss
    wph
    @39
    cB
    cxr
    wcel
    #
    wph
    cU
    @38
    wcel
    #
    @38
    c0
    wne
    @39
    @41
    wa
    #
    dvferm.u
    @38
    cU
    ne0i
    @43
    @38
    c0
    cA
    cB
    ndmioo
    necon1ai
    3syl
    #
    simpld
    #
    wph
    cA
    cU
    clt
    wbr
    #
    @40
    wph
    @46
    cU
    cB
    clt
    wbr
    #
    wph
    @42
    @46
    @47
    wa
    dvferm.u
    cU
    cA
    cB
    eliooord
    syl
    #
    simpld
    wph
    @39
    cU
    cxr
    wcel
    #
    @46
    @40
    wi
    @45
    wph
    cU
    wph
    @38
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
    cA
    cU
    xrltle
    syl2anc
    mpd
    cA
    cU
    cB
    iooss1
    syl2anc
    dvferm.s
    sstrd
    wph
    cS
    @37
    wcel
    #
    cS
    cr
    wcel
    #
    cU
    cS
    clt
    wbr
    #
    cS
    cB
    clt
    wbr
    #
    wph
    cS
    cU
    cB
    cU
    cT
    caddc
    co
    #
    cle
    wbr
    #
    cB
    @56
    cif
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cr
    dvferm1.x
    wph
    @59
    wph
    cU
    @58
    @50
    wph
    @58
    cxr
    wcel
    @56
    cr
    wcel
    #
    cmnf
    @58
    clt
    wbr
    #
    @58
    @56
    cle
    wbr
    #
    @58
    cr
    wcel
    #
    wph
    @57
    cB
    @56
    cxr
    wph
    @39
    @41
    @44
    simprd
    #
    wph
    @56
    wph
    cU
    cT
    @50
    wph
    cT
    dvferm1.t
    rpred
    #
    readdcld
    #
    rexrd
    #
    ifcld
    #
    @67
    wph
    cmnf
    cB
    clt
    wbr
    #
    cmnf
    @56
    clt
    wbr
    #
    @62
    wph
    cmnf
    cU
    cB
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    @51
    @65
    wph
    cU
    cr
    wcel
    #
    cmnf
    cU
    clt
    wbr
    @50
    cU
    mnflt
    syl
    wph
    @46
    @47
    @48
    simprd
    #
    xrlttrd
    wph
    @61
    @71
    @67
    @56
    mnflt
    syl
    @57
    @70
    @71
    @62
    cB
    @56
    cB
    @58
    cmnf
    clt
    breq2
    @56
    @58
    cmnf
    clt
    breq2
    ifboth
    syl2anc
    wph
    @41
    @56
    cxr
    wcel
    #
    @63
    @65
    @68
    cB
    @56
    xrmin2
    syl2anc
    #
    @58
    @56
    xrre
    syl22anc
    #
    readdcld
    rehalfcld
    syl5eqel
    #
    wph
    cU
    @60
    cS
    clt
    wph
    cU
    @58
    clt
    wbr
    #
    cU
    @60
    clt
    wbr
    #
    wph
    @47
    cU
    @56
    clt
    wbr
    #
    @78
    @73
    wph
    cU
    cT
    @50
    dvferm1.t
    ltaddrpd
    @57
    @47
    @80
    @78
    cB
    @56
    cB
    @58
    cU
    clt
    breq2
    @56
    @58
    cU
    clt
    breq2
    ifboth
    syl2anc
    #
    wph
    @72
    @64
    @78
    @79
    wb
    @50
    @76
    cU
    @58
    avglt1
    syl2anc
    mpbid
    dvferm1.x
    syl6breqr
    #
    wph
    cS
    @58
    cB
    wph
    cS
    @77
    rexrd
    @69
    @65
    wph
    cS
    @60
    @58
    clt
    dvferm1.x
    wph
    @78
    @60
    @58
    clt
    wbr
    #
    @81
    wph
    @72
    @64
    @78
    @83
    wb
    @50
    @76
    cU
    @58
    avglt2
    syl2anc
    mpbid
    syl5eqbr
    #
    wph
    @41
    @74
    @58
    cB
    cle
    wbr
    @65
    @68
    cB
    @56
    xrmin1
    syl2anc
    xrltletrd
    wph
    @49
    @41
    @52
    @53
    @54
    @55
    w3a
    wb
    @51
    @65
    cU
    cB
    cS
    elioo2
    syl2anc
    mpbir3and
    #
    sseldd
    #
    wph
    cU
    cS
    @50
    @82
    gtned
    #
    cS
    cX
    cU
    eldifsn
    sylanbrc
    dvferm1.l
    wph
    @33
    @35
    @87
    wph
    @34
    @5
    cT
    clt
    wph
    cU
    cS
    @50
    @77
    wph
    cU
    cS
    @50
    @77
    @82
    ltled
    abssubge0d
    wph
    @5
    cT
    clt
    wbr
    cS
    @56
    clt
    wbr
    wph
    cS
    @58
    @56
    @77
    @76
    @67
    @84
    @75
    ltletrd
    wph
    cS
    cU
    cT
    @77
    @50
    @66
    ltsubadd2d
    mpbird
    eqbrtrd
    jca
    @32
    @36
    @17
    wi
    vz
    cS
    @18
    @20
    cS
    wceq
    #
    @25
    @36
    @31
    @17
    @88
    @21
    @33
    @24
    @35
    @20
    cS
    cU
    neeq1
    @88
    @23
    @34
    cT
    clt
    @88
    @22
    @5
    cabs
    @20
    cS
    cU
    cmin
    oveq1
    #
    fveq2d
    breq1d
    anbi12d
    @88
    @30
    @16
    @9
    clt
    @88
    @29
    @15
    cabs
    @88
    @28
    @6
    @9
    cmin
    @88
    @27
    @3
    @22
    @5
    cdiv
    @88
    @26
    @1
    @0
    cmin
    @20
    cS
    cF
    fveq2
    oveq1d
    @89
    oveq12d
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl3c
    wph
    @6
    @9
    @9
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
    @86
    ffvelrnd
    #
    wph
    cX
    cr
    cU
    cF
    dvferm.a
    wph
    @38
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
    @5
    wph
    cS
    cU
    @77
    @50
    resubcld
    #
    wph
    @54
    cc0
    @5
    clt
    wbr
    #
    @82
    wph
    cU
    cS
    @50
    @77
    posdifd
    mpbid
    #
    elrpd
    rerpdivcld
    @12
    @12
    absdifltd
    mpbid
    simpld
    eqbrtrrd
    wph
    @3
    cr
    wcel
    @5
    cr
    wcel
    @94
    @4
    @7
    wb
    @92
    @93
    @95
    @3
    @5
    gt0div
    syl3anc
    mpbird
    wph
    @0
    @1
    @91
    @90
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
    @52
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
    @37
    wral
    @96
    @85
    dvferm1.r
    @99
    @96
    vy
    cS
    @37
    @97
    cS
    wceq
    @98
    @1
    @0
    cle
    @97
    cS
    cF
    fveq2
    breq1d
    rspcv
    sylc
    wph
    @1
    @0
    @90
    @91
    lenltd
    mpbid
    pm2.65i
end
