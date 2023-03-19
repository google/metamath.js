include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "wn.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cz.mm"
include "wrex.mm"
include "simpr.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "syl6bb.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnred.mm"
include "bezoutlem2.mm"
include "syl5bb.mm"
include "nnrpd.mm"
include "adantr.mm"
include "modlt.mm"
include "syl2anc.mm"
include "nnzd.mm"
include "zmodcld.mm"
include "nn0red.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "nndivred.mm"
include "flcld.mm"
include "zmulcld.mm"
include "zsubcld.mm"
include "simprlr.mm"
include "simprrr.mm"
include "cc.mm"
include "zcnd.mm"
include "mulcld.mm"
include "addsub4d.mm"
include "adddird.mm"
include "mulassd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "subdid.mm"
include "3eqtr4d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "oveq1.mm"
include "oveq12.mm"
include "sylan2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "expcomd.mm"
include "expr.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "ex.mm"
include "modval.mm"
include "eqcomd.mm"
include "simplbi2com.mm"
include "syl.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "infssuzle.mm"
include "mpan.mm"
include "syl5eqbr.mm"
include "syl6.mm"
include "mtod.mm"
include "cn0.mm"
include "wo.mm"
include "elnn0.mm"
include "ord.mm"
include "wb.mm"
include "dvdsval3.mm"
include "mpbird.mm"

theorem bezoutlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
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
  disjoint C x
  disjoint C y
  disjoint C z
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
  assert |- ( ph -> ( C e. M -> G || C ) )

  proof
    wph
    cC
    cM
    wcel
    #
    cG
    cC
    cdvds
    wbr
    #
    wph
    @0
    wa
    #
    @1
    cC
    cG
    cmo
    co
    #
    cc0
    wceq
    #
    @2
    @3
    cn
    wcel
    #
    wn
    @4
    @2
    @5
    cG
    @3
    cle
    wbr
    #
    @2
    @3
    cG
    clt
    wbr
    #
    @6
    wn
    @2
    cC
    cr
    wcel
    #
    cG
    crp
    wcel
    #
    @7
    @2
    cC
    @2
    cC
    cn
    wcel
    #
    cC
    cA
    vs
    cv
    #
    cmul
    co
    #
    cB
    vt
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
    vt
    cz
    wrex
    vs
    cz
    wrex
    #
    @2
    @0
    @10
    @17
    wa
    wph
    @0
    simpr
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
    @17
    vz
    cC
    cn
    cM
    @18
    cC
    wceq
    #
    @25
    cC
    @23
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    @17
    @26
    @24
    @27
    vx
    vy
    cz
    cz
    @18
    cC
    @23
    eqeq1
    2rexbidv
    @27
    @16
    cC
    @12
    @22
    caddc
    co
    #
    wceq
    vx
    vy
    vs
    vt
    cz
    cz
    @19
    @11
    wceq
    #
    @23
    @28
    cC
    @29
    @20
    @12
    @22
    caddc
    @19
    @11
    cA
    cmul
    oveq2
    oveq1d
    eqeq2d
    @21
    @13
    wceq
    #
    @28
    @15
    cC
    @30
    @22
    @14
    @12
    caddc
    @21
    @13
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    cbvrex2v
    syl6bb
    bezout.1
    elrab2
    sylib
    #
    simpld
    #
    nnred
    #
    wph
    @9
    @0
    wph
    cG
    wph
    cG
    cn
    wcel
    #
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
    wph
    cG
    cM
    wcel
    @34
    @41
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
    @25
    @41
    vz
    cG
    cn
    cM
    @25
    @18
    @39
    wceq
    #
    vv
    cz
    wrex
    vu
    cz
    wrex
    @18
    cG
    wceq
    #
    @41
    @24
    @42
    @18
    @36
    @22
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
    @19
    @35
    wceq
    #
    @23
    @44
    @18
    @45
    @20
    @36
    @22
    caddc
    @19
    @35
    cA
    cmul
    oveq2
    oveq1d
    eqeq2d
    @21
    @37
    wceq
    #
    @44
    @39
    @18
    @46
    @22
    @38
    @36
    caddc
    @21
    @37
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    cbvrex2v
    @43
    @42
    @40
    vu
    vv
    cz
    cz
    @18
    cG
    @39
    eqeq1
    2rexbidv
    syl5bb
    bezout.1
    elrab2
    sylib
    #
    simpld
    #
    nnrpd
    adantr
    #
    cC
    cG
    modlt
    syl2anc
    @2
    @3
    cG
    @2
    @3
    @2
    cC
    cG
    @2
    cC
    @32
    nnzd
    #
    wph
    @34
    @0
    @48
    adantr
    #
    zmodcld
    #
    nn0red
    wph
    cG
    cr
    wcel
    @0
    wph
    cG
    @48
    nnred
    adantr
    ltnled
    mpbid
    @2
    @5
    @3
    cM
    wcel
    #
    @6
    @2
    @3
    @23
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @5
    @53
    wi
    @2
    cC
    cG
    cC
    cG
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @23
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @55
    @2
    @17
    @61
    @2
    @10
    @17
    @31
    simprd
    @2
    @16
    @61
    vs
    vt
    cz
    cz
    @2
    @11
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    wa
    #
    @16
    @61
    wi
    #
    @2
    @64
    wa
    #
    @41
    @65
    wph
    @41
    @0
    @64
    wph
    @34
    @41
    @47
    simprd
    ad2antrr
    @66
    @40
    @65
    vu
    vv
    cz
    cz
    @2
    @64
    @35
    cz
    wcel
    #
    @37
    cz
    wcel
    #
    wa
    #
    @40
    @65
    wi
    @2
    @64
    @69
    wa
    #
    wa
    #
    @16
    @40
    @61
    @71
    @61
    @16
    @40
    wa
    #
    @15
    @39
    @57
    cmul
    co
    #
    cmin
    co
    #
    @23
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @71
    @11
    @35
    @57
    cmul
    co
    #
    cmin
    co
    #
    cz
    wcel
    @13
    @37
    @57
    cmul
    co
    #
    cmin
    co
    #
    cz
    wcel
    @74
    cA
    @78
    cmul
    co
    #
    cB
    @80
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @76
    @71
    @11
    @77
    @2
    @62
    @63
    @69
    simprll
    #
    @71
    @35
    @57
    @2
    @64
    @67
    @68
    simprrl
    #
    @2
    @57
    cz
    wcel
    @70
    @2
    @56
    @2
    cC
    cG
    @33
    @51
    nndivred
    flcld
    #
    adantr
    #
    zmulcld
    #
    zsubcld
    @71
    @13
    @79
    @2
    @62
    @63
    @69
    simprlr
    #
    @71
    @37
    @57
    @2
    @64
    @67
    @68
    simprrr
    #
    @88
    zmulcld
    #
    zsubcld
    @71
    @15
    cA
    @77
    cmul
    co
    #
    cB
    @79
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    @12
    @93
    cmin
    co
    #
    @14
    @94
    cmin
    co
    #
    caddc
    co
    @74
    @83
    @71
    @12
    @14
    @93
    @94
    @71
    cA
    @11
    wph
    cA
    cc
    wcel
    @0
    @70
    wph
    cA
    bezout.3
    zcnd
    ad2antrr
    #
    @71
    @11
    @85
    zcnd
    #
    mulcld
    @71
    cB
    @13
    wph
    cB
    cc
    wcel
    @0
    @70
    wph
    cB
    bezout.4
    zcnd
    ad2antrr
    #
    @71
    @13
    @90
    zcnd
    #
    mulcld
    @71
    cA
    @77
    @98
    @71
    @77
    @89
    zcnd
    #
    mulcld
    @71
    cB
    @79
    @100
    @71
    @79
    @92
    zcnd
    #
    mulcld
    addsub4d
    @71
    @73
    @95
    @15
    cmin
    @71
    @73
    @36
    @57
    cmul
    co
    #
    @38
    @57
    cmul
    co
    #
    caddc
    co
    @95
    @71
    @36
    @38
    @57
    @71
    cA
    @35
    @98
    @71
    @35
    @86
    zcnd
    #
    mulcld
    @71
    cB
    @37
    @100
    @71
    @37
    @91
    zcnd
    #
    mulcld
    @2
    @57
    cc
    wcel
    @70
    @2
    @57
    @87
    zcnd
    adantr
    #
    adddird
    @71
    @104
    @93
    @105
    @94
    caddc
    @71
    cA
    @35
    @57
    @98
    @106
    @108
    mulassd
    @71
    cB
    @37
    @57
    @100
    @107
    @108
    mulassd
    oveq12d
    eqtrd
    oveq2d
    @71
    @81
    @96
    @82
    @97
    caddc
    @71
    cA
    @11
    @77
    @98
    @99
    @102
    subdid
    @71
    cB
    @13
    @79
    @100
    @101
    @103
    subdid
    oveq12d
    3eqtr4d
    @75
    @84
    @74
    @81
    @22
    caddc
    co
    #
    wceq
    vx
    vy
    @78
    @80
    cz
    cz
    @19
    @78
    wceq
    #
    @23
    @109
    @74
    @110
    @20
    @81
    @22
    caddc
    @19
    @78
    cA
    cmul
    oveq2
    oveq1d
    eqeq2d
    @21
    @80
    wceq
    #
    @109
    @83
    @74
    @111
    @22
    @82
    @81
    caddc
    @21
    @80
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    rspc2ev
    syl3anc
    @72
    @60
    @75
    vx
    vy
    cz
    cz
    @72
    @59
    @74
    @23
    @40
    @16
    @58
    @73
    wceq
    @59
    @74
    wceq
    cG
    @39
    @57
    cmul
    oveq1
    cC
    @15
    @58
    @73
    cmin
    oveq12
    sylan2
    eqeq1d
    2rexbidv
    syl5ibrcom
    expcomd
    expr
    rexlimdvv
    mpd
    ex
    rexlimdvv
    mpd
    @2
    @60
    @54
    vx
    vy
    cz
    cz
    @2
    @59
    @3
    @23
    @2
    @3
    @59
    @2
    @8
    @9
    @3
    @59
    wceq
    @33
    @49
    cC
    cG
    modval
    syl2anc
    eqcomd
    eqeq1d
    2rexbidv
    mpbid
    @53
    @5
    @55
    @25
    @55
    vz
    @3
    cn
    cM
    @18
    @3
    wceq
    @24
    @54
    vx
    vy
    cz
    cz
    @18
    @3
    @23
    eqeq1
    2rexbidv
    bezout.1
    elrab2
    simplbi2com
    syl
    @53
    cG
    cM
    cr
    clt
    cinf
    #
    @3
    cle
    bezout.2
    cM
    c1
    cuz
    cfv
    #
    wss
    @53
    @112
    @3
    cle
    wbr
    cM
    cn
    @113
    cM
    @25
    vz
    cn
    crab
    cn
    bezout.1
    @25
    vz
    cn
    ssrab2
    eqsstri
    nnuz
    sseqtri
    @3
    cM
    c1
    infssuzle
    mpan
    syl5eqbr
    syl6
    mtod
    @2
    @5
    @4
    @2
    @3
    cn0
    wcel
    @5
    @4
    wo
    @52
    @3
    elnn0
    sylib
    ord
    mpd
    @2
    @34
    cC
    cz
    wcel
    @1
    @4
    wb
    @51
    @50
    cG
    cC
    dvdsval3
    syl2anc
    mpbird
    ex
end
