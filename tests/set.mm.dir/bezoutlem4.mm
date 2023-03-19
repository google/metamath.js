include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "cv.mm"
include "cmul.mm"
include "cz.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "wb.mm"
include "gcdcld.mm"
include "nn0zd.mm"
include "divides.mm"
include "mpbid.mm"
include "simprd.mm"
include "reeanv.mm"
include "caddc.mm"
include "wi.mm"
include "cn.mm"
include "bezoutlem2.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprrl.mm"
include "simprll.mm"
include "zmulcld.mm"
include "simprrr.mm"
include "simprlr.mm"
include "zaddcld.mm"
include "adantr.mm"
include "dvdsmul2.mm"
include "zcnd.mm"
include "adddird.mm"
include "mul32d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "breq2.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "com23.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "dvdsle.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "bezoutlem1.mm"
include "bezoutlem3.mm"
include "syld.mm"
include "nnzd.mm"
include "dvdsabsb.mm"
include "sylibrd.mm"
include "imp.mm"
include "dvds0.mm"
include "syl.mm"
include "pm2.61ne.mm"
include "crab.mm"
include "eqid.mm"
include "rexcom.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antll.mm"
include "mulcld.mm"
include "ad2antrl.mm"
include "addcomd.mm"
include "2rexbidva.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "wn.mm"
include "dvdslegcd.mm"
include "syl31anc.mm"
include "nn0red.mm"
include "nnred.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem bezoutlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cG: class G
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cC: class C
  assume bezout.1: |- M = { z e. NN | E. x e. ZZ E. y e. ZZ z = ( ( A x. x ) + ( B x. y ) ) }
  assume bezout.3: |- ( ph -> A e. ZZ )
  assume bezout.4: |- ( ph -> B e. ZZ )
  assume bezout.2: |- G = inf ( M , RR , < )
  assume bezout.5: |- ( ph -> -. ( A = 0 /\ B = 0 ) )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint M x
  disjoint M y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint M s
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B v
  assert |- ( ph -> ( A gcd B ) e. M )

  proof
    wph
    cA
    cB
    cgcd
    co
    #
    cG
    cM
    wph
    @0
    cG
    wceq
    @0
    cG
    cle
    wbr
    #
    cG
    @0
    cle
    wbr
    #
    wph
    @0
    cG
    cdvds
    wbr
    #
    @1
    wph
    vs
    cv
    #
    @0
    cmul
    co
    #
    cA
    wceq
    #
    vs
    cz
    wrex
    #
    vt
    cv
    #
    @0
    cmul
    co
    #
    cB
    wceq
    #
    vt
    cz
    wrex
    #
    @3
    wph
    @0
    cA
    cdvds
    wbr
    #
    @7
    wph
    @12
    @0
    cB
    cdvds
    wbr
    #
    wph
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @12
    @13
    wa
    bezout.3
    bezout.4
    cA
    cB
    gcddvds
    syl2anc
    #
    simpld
    wph
    @0
    cz
    wcel
    #
    @14
    @12
    @7
    wb
    wph
    @0
    wph
    cA
    cB
    bezout.3
    bezout.4
    gcdcld
    #
    nn0zd
    #
    bezout.3
    vs
    @0
    cA
    divides
    syl2anc
    mpbid
    wph
    @13
    @11
    wph
    @12
    @13
    @16
    simprd
    wph
    @17
    @15
    @13
    @11
    wb
    @19
    bezout.4
    vt
    @0
    cB
    divides
    syl2anc
    mpbid
    @7
    @11
    wa
    @6
    @10
    wa
    #
    vt
    cz
    wrex
    vs
    cz
    wrex
    wph
    @3
    @6
    @10
    vs
    vt
    cz
    cz
    reeanv
    wph
    @20
    @3
    vs
    vt
    cz
    cz
    wph
    cG
    cA
    vu
    cv
    #
    cmul
    co
    #
    cB
    vv
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
    vv
    cz
    wrex
    vu
    cz
    wrex
    #
    @4
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    wa
    #
    @20
    @3
    wi
    #
    wi
    #
    wph
    cG
    cn
    wcel
    #
    @27
    wph
    cG
    cM
    wcel
    @33
    @27
    wa
    wph
    vx
    vy
    vz
    cA
    cB
    cG
    cM
    bezout.1
    bezout.3
    bezout.4
    bezout.2
    bezout.5
    bezoutlem2
    #
    vz
    cv
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    cB
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
    cz
    wrex
    vx
    cz
    wrex
    #
    @27
    vz
    cG
    cn
    cM
    @42
    @35
    @25
    wceq
    #
    vv
    cz
    wrex
    vu
    cz
    wrex
    @35
    cG
    wceq
    #
    @27
    @41
    @43
    @35
    @22
    @39
    caddc
    co
    #
    wceq
    vx
    vy
    vu
    vv
    cz
    cz
    vx
    vu
    weq
    #
    @40
    @45
    @35
    @46
    @37
    @22
    @39
    caddc
    @36
    @21
    cA
    cmul
    oveq2
    oveq1d
    eqeq2d
    vy
    vv
    weq
    #
    @45
    @25
    @35
    @47
    @39
    @24
    @22
    caddc
    @38
    @23
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    cbvrex2v
    @44
    @43
    @26
    vu
    vv
    cz
    cz
    @35
    cG
    @25
    eqeq1
    2rexbidv
    syl5bb
    bezout.1
    elrab2
    sylib
    #
    simprd
    wph
    @26
    @32
    vu
    vv
    cz
    cz
    wph
    @21
    cz
    wcel
    #
    @23
    cz
    wcel
    #
    wa
    #
    wa
    @30
    @26
    @31
    wph
    @51
    @30
    @26
    @31
    wi
    wph
    @51
    @30
    wa
    #
    wa
    #
    @31
    @26
    @20
    @0
    @25
    cdvds
    wbr
    #
    wi
    @53
    @0
    @5
    @21
    cmul
    co
    #
    @9
    @23
    cmul
    co
    #
    caddc
    co
    #
    cdvds
    wbr
    @20
    @54
    @53
    @0
    @4
    @21
    cmul
    co
    #
    @8
    @23
    cmul
    co
    #
    caddc
    co
    #
    @0
    cmul
    co
    #
    @57
    cdvds
    @53
    @60
    cz
    wcel
    @17
    @0
    @61
    cdvds
    wbr
    @53
    @58
    @59
    @53
    @4
    @21
    wph
    @51
    @28
    @29
    simprrl
    #
    wph
    @49
    @50
    @30
    simprll
    #
    zmulcld
    #
    @53
    @8
    @23
    wph
    @51
    @28
    @29
    simprrr
    #
    wph
    @49
    @50
    @30
    simprlr
    #
    zmulcld
    #
    zaddcld
    wph
    @17
    @52
    @19
    adantr
    #
    @60
    @0
    dvdsmul2
    syl2anc
    @53
    @61
    @58
    @0
    cmul
    co
    #
    @59
    @0
    cmul
    co
    #
    caddc
    co
    @57
    @53
    @58
    @59
    @0
    @53
    @58
    @64
    zcnd
    @53
    @59
    @67
    zcnd
    @53
    @0
    @68
    zcnd
    #
    adddird
    @53
    @69
    @55
    @70
    @56
    caddc
    @53
    @4
    @21
    @0
    @53
    @4
    @62
    zcnd
    @53
    @21
    @63
    zcnd
    @71
    mul32d
    @53
    @8
    @23
    @0
    @53
    @8
    @65
    zcnd
    @53
    @23
    @66
    zcnd
    @71
    mul32d
    oveq12d
    eqtrd
    breqtrd
    @20
    @57
    @25
    @0
    cdvds
    @6
    @10
    @55
    @22
    @56
    @24
    caddc
    @5
    cA
    @21
    cmul
    oveq1
    @9
    cB
    @23
    cmul
    oveq1
    oveqan12d
    breq2d
    syl5ibcom
    @26
    @3
    @54
    @20
    cG
    @25
    @0
    cdvds
    breq2
    imbi2d
    syl5ibrcom
    expr
    com23
    rexlimdvva
    mpd
    rexlimdvv
    syl5bir
    mp2and
    wph
    @17
    @33
    @3
    @1
    wi
    @19
    wph
    @33
    @27
    @48
    simpld
    #
    @0
    cG
    dvdsle
    syl2anc
    mpd
    wph
    cG
    cA
    cdvds
    wbr
    #
    cG
    cB
    cdvds
    wbr
    #
    @2
    wph
    @73
    cG
    cc0
    cdvds
    wbr
    #
    cA
    cc0
    cA
    cc0
    cG
    cdvds
    breq2
    wph
    cA
    cc0
    wne
    #
    @73
    wph
    @76
    cG
    cA
    cabs
    cfv
    #
    cdvds
    wbr
    #
    @73
    wph
    @76
    @77
    cM
    wcel
    @78
    wph
    vx
    vy
    vz
    cA
    cB
    cM
    bezout.1
    bezout.3
    bezout.4
    bezoutlem1
    wph
    vx
    vy
    vz
    cA
    cB
    @77
    cG
    cM
    bezout.1
    bezout.3
    bezout.4
    bezout.2
    bezout.5
    bezoutlem3
    syld
    wph
    cG
    cz
    wcel
    #
    @14
    @73
    @78
    wb
    wph
    cG
    @72
    nnzd
    #
    bezout.3
    cG
    cA
    dvdsabsb
    syl2anc
    sylibrd
    imp
    wph
    @79
    @75
    @80
    cG
    dvds0
    syl
    #
    pm2.61ne
    wph
    @74
    @75
    cB
    cc0
    cB
    cc0
    cG
    cdvds
    breq2
    wph
    cB
    cc0
    wne
    #
    @74
    wph
    @82
    cG
    cB
    cabs
    cfv
    #
    cdvds
    wbr
    #
    @74
    wph
    @82
    @83
    cM
    wcel
    #
    @84
    wph
    @82
    @83
    @35
    @39
    @37
    caddc
    co
    #
    wceq
    #
    vx
    cz
    wrex
    vy
    cz
    wrex
    #
    vz
    cn
    crab
    #
    wcel
    @85
    wph
    vy
    vx
    vz
    cB
    cA
    @89
    @89
    eqid
    bezout.4
    bezout.3
    bezoutlem1
    wph
    cM
    @89
    @83
    wph
    cM
    @42
    vz
    cn
    crab
    @89
    bezout.1
    wph
    @42
    @88
    vz
    cn
    @42
    @41
    vx
    cz
    wrex
    vy
    cz
    wrex
    wph
    @88
    @41
    vx
    vy
    cz
    cz
    rexcom
    wph
    @41
    @87
    vy
    vx
    cz
    cz
    wph
    @38
    cz
    wcel
    #
    @36
    cz
    wcel
    #
    wa
    #
    wa
    #
    @40
    @86
    @35
    @93
    @37
    @39
    @93
    cA
    @36
    wph
    cA
    cc
    wcel
    @92
    wph
    cA
    bezout.3
    zcnd
    adantr
    @91
    @36
    cc
    wcel
    wph
    @90
    @36
    zcn
    ad2antll
    mulcld
    @93
    cB
    @38
    wph
    cB
    cc
    wcel
    @92
    wph
    cB
    bezout.4
    zcnd
    adantr
    @90
    @38
    cc
    wcel
    wph
    @91
    @38
    zcn
    ad2antrl
    mulcld
    addcomd
    eqeq2d
    2rexbidva
    syl5bb
    rabbidv
    syl5eq
    eleq2d
    sylibrd
    wph
    vx
    vy
    vz
    cA
    cB
    @83
    cG
    cM
    bezout.1
    bezout.3
    bezout.4
    bezout.2
    bezout.5
    bezoutlem3
    syld
    wph
    @79
    @15
    @74
    @84
    wb
    @80
    bezout.4
    cG
    cB
    dvdsabsb
    syl2anc
    sylibrd
    imp
    @81
    pm2.61ne
    wph
    @79
    @14
    @15
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    wn
    @73
    @74
    wa
    @2
    wi
    @80
    bezout.3
    bezout.4
    bezout.5
    cG
    cA
    cB
    dvdslegcd
    syl31anc
    mp2and
    wph
    @0
    cG
    wph
    @0
    @18
    nn0red
    wph
    cG
    @72
    nnred
    letri3d
    mpbir2and
    @34
    eqeltrd
end
