include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "clt.mm"
include "wn.mm"
include "sqrlem6.mm"
include "cmin.mm"
include "c3.mm"
include "cdiv.mm"
include "caddc.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "sqrlem3.mm"
include "adantr.mm"
include "sqrlem4.mm"
include "simpld.mm"
include "rpre.mm"
include "syl.mm"
include "resqcld.mm"
include "resubcld.mm"
include "cc0.mm"
include "posdifd.mm"
include "biimpa.mm"
include "elrpd.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "rpdivcl.mm"
include "sylancl.mm"
include "rpaddcld.mm"
include "cmul.mm"
include "cc.mm"
include "recnd.mm"
include "cn.mm"
include "3nn.mm"
include "nndivre.mm"
include "binom2.mm"
include "syl2anc.mm"
include "2re.mm"
include "remulcld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "addassd.mm"
include "eqtrd.mm"
include "2cn.mm"
include "mulass.mm"
include "mp3an1.mm"
include "eqcomd.mm"
include "sqvald.mm"
include "oveq12d.mm"
include "adddird.mm"
include "eqtr4d.mm"
include "simprd.mm"
include "wb.mm"
include "2pos.mm"
include "1re.mm"
include "lemul2.mm"
include "mp3an2.mm"
include "mpanr12.mm"
include "mpbid.mm"
include "2t1e2.mm"
include "syl6breq.mm"
include "a1i.mm"
include "sqge0d.mm"
include "addge01d.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "simplr.mm"
include "letrd.mm"
include "1le3.mm"
include "wi.mm"
include "letr.mm"
include "mp3an23.mm"
include "mpan2i.mm"
include "mpd.mm"
include "3t1e3.mm"
include "syl6breqr.mm"
include "ledivmul.mm"
include "le2add.mm"
include "mp2and.mm"
include "df-3.mm"
include "readdcld.mm"
include "lemul1d.mm"
include "3cn.mm"
include "3ne0.mm"
include "divcan2.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "leaddsub2d.mm"
include "oveq1.mm"
include "breq1d.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "csup.mm"
include "suprub.mm"
include "rpgt0d.mm"
include "ltaddposd.mm"
include "ltnled.mm"
include "bitrd.mm"
include "syldan.mm"
include "pm2.65da.mm"
include "eqleltd.mm"
include "mpbir2and.mm"

theorem sqrlem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )
  assume sqrlem5.3: |- T = { y | E. a e. S E. b e. S y = ( a x. b ) }

  disjoint a b
  disjoint a y
  disjoint S a
  disjoint b y
  disjoint S b
  disjoint S y
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b z
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint S u
  disjoint v y
  disjoint v z
  disjoint S v
  disjoint y z
  disjoint S z
  disjoint v x
  disjoint A v
  disjoint x z
  disjoint A z
  disjoint B v
  disjoint B z
  disjoint T u
  disjoint T v
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> ( B ^ 2 ) = A )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    wa
    #
    cB
    c2
    cexp
    co
    #
    cA
    wceq
    @3
    cA
    cle
    wbr
    @3
    cA
    clt
    wbr
    #
    wn
    vx
    vy
    cA
    cB
    cS
    cT
    va
    vb
    sqrlem1.1
    sqrlem1.2
    sqrlem5.3
    sqrlem6
    @2
    @4
    cB
    cA
    @3
    cmin
    co
    #
    c3
    cdiv
    co
    #
    caddc
    co
    #
    cB
    cle
    wbr
    #
    @2
    @4
    wa
    #
    cS
    cr
    wss
    cS
    c0
    wne
    vz
    cv
    vy
    cv
    #
    cle
    wbr
    vz
    cS
    wral
    vy
    cr
    wrex
    w3a
    #
    @7
    cS
    wcel
    #
    @8
    @2
    @11
    @4
    vx
    vz
    vy
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem3
    adantr
    @9
    @7
    crp
    wcel
    @7
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    @12
    @9
    cB
    @6
    @9
    cB
    crp
    wcel
    #
    cB
    c1
    cle
    wbr
    #
    @2
    @15
    @16
    wa
    #
    @4
    vx
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem4
    #
    adantr
    simpld
    @9
    @5
    crp
    wcel
    c3
    crp
    wcel
    @6
    crp
    wcel
    @9
    @5
    @2
    @5
    cr
    wcel
    #
    @4
    @2
    cA
    @3
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    rpre
    adantr
    #
    @2
    cB
    @2
    @17
    cB
    cr
    wcel
    #
    @18
    @15
    @22
    @16
    cB
    rpre
    adantr
    syl
    #
    resqcld
    #
    resubcld
    #
    adantr
    #
    @2
    @4
    cc0
    @5
    clt
    wbr
    @2
    @3
    cA
    @24
    @21
    posdifd
    biimpa
    elrpd
    c3
    3re
    3pos
    elrpii
    @5
    c3
    rpdivcl
    sylancl
    #
    rpaddcld
    @9
    @13
    @3
    c2
    cB
    @6
    cmul
    co
    #
    cmul
    co
    #
    @6
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    cA
    cle
    @9
    @13
    @3
    @29
    caddc
    co
    @30
    caddc
    co
    #
    @32
    @9
    cB
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @13
    @33
    wceq
    @9
    cB
    @2
    @22
    @4
    @23
    adantr
    #
    recnd
    #
    @9
    @6
    @2
    @6
    cr
    wcel
    #
    @4
    @2
    @19
    c3
    cn
    wcel
    @38
    @25
    3nn
    @5
    c3
    nndivre
    sylancl
    #
    adantr
    #
    recnd
    #
    cB
    @6
    binom2
    syl2anc
    @9
    @3
    @29
    @30
    @9
    @3
    @2
    @3
    cr
    wcel
    @4
    @24
    adantr
    #
    recnd
    @9
    @29
    @9
    c2
    cr
    wcel
    #
    @28
    cr
    wcel
    @29
    cr
    wcel
    2re
    @9
    cB
    @6
    @36
    @40
    remulcld
    c2
    @28
    remulcl
    sylancr
    #
    recnd
    @9
    @30
    @9
    @6
    @40
    resqcld
    #
    recnd
    addassd
    eqtrd
    @9
    @32
    cA
    cle
    wbr
    @31
    @5
    cle
    wbr
    @9
    @31
    c2
    cB
    cmul
    co
    #
    @6
    caddc
    co
    #
    @6
    cmul
    co
    #
    @5
    cle
    @9
    @31
    @46
    @6
    cmul
    co
    #
    @6
    @6
    cmul
    co
    #
    caddc
    co
    @48
    @9
    @29
    @49
    @30
    @50
    caddc
    @9
    @49
    @29
    @9
    @34
    @35
    @49
    @29
    wceq
    #
    @37
    @41
    c2
    cc
    wcel
    @34
    @35
    @51
    2cn
    c2
    cB
    @6
    mulass
    mp3an1
    syl2anc
    eqcomd
    @9
    @6
    @41
    sqvald
    oveq12d
    @9
    @46
    @6
    @6
    @9
    @46
    @9
    @43
    @22
    @46
    cr
    wcel
    #
    2re
    @36
    c2
    cB
    remulcl
    sylancr
    #
    recnd
    @41
    @41
    adddird
    eqtr4d
    @9
    @48
    c3
    @6
    cmul
    co
    #
    @5
    cle
    @9
    @47
    c3
    cle
    wbr
    @48
    @54
    cle
    wbr
    @9
    @47
    c2
    c1
    caddc
    co
    #
    c3
    cle
    @9
    @46
    c2
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    @47
    @55
    cle
    wbr
    #
    @9
    @46
    c2
    c1
    cmul
    co
    #
    c2
    cle
    @2
    @46
    @59
    cle
    wbr
    #
    @4
    @2
    @16
    @60
    @2
    @15
    @16
    @18
    simprd
    @2
    @22
    @16
    @60
    wb
    #
    @23
    @22
    @43
    cc0
    c2
    clt
    wbr
    #
    @61
    2re
    2pos
    @22
    c1
    cr
    wcel
    #
    @43
    @62
    wa
    @61
    1re
    cB
    c1
    c2
    lemul2
    mp3an2
    mpanr12
    syl
    mpbid
    adantr
    2t1e2
    syl6breq
    @9
    @57
    @5
    c3
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @9
    @5
    c3
    @64
    cle
    @9
    @5
    c1
    cle
    wbr
    #
    @5
    c3
    cle
    wbr
    #
    @9
    @5
    cA
    c1
    @26
    @2
    @20
    @4
    @21
    adantr
    #
    @63
    @9
    1re
    a1i
    @9
    @5
    cA
    cle
    wbr
    cA
    cA
    @3
    caddc
    co
    cle
    wbr
    #
    @9
    cc0
    @3
    cle
    wbr
    @69
    @9
    cB
    @36
    sqge0d
    @9
    cA
    @3
    @68
    @42
    addge01d
    mpbid
    @9
    cA
    @3
    cA
    @68
    @42
    @68
    lesubaddd
    mpbird
    @0
    @1
    @4
    simplr
    letrd
    @9
    @66
    c1
    c3
    cle
    wbr
    #
    @67
    1le3
    @9
    @19
    @66
    @70
    wa
    @67
    wi
    #
    @26
    @19
    @63
    c3
    cr
    wcel
    #
    @71
    1re
    3re
    @5
    c1
    c3
    letr
    mp3an23
    syl
    mpan2i
    mpd
    3t1e3
    syl6breqr
    @9
    @19
    @57
    @65
    wb
    #
    @26
    @19
    @72
    cc0
    c3
    clt
    wbr
    #
    @73
    3re
    3pos
    @19
    @63
    @72
    @74
    wa
    @73
    1re
    @5
    c1
    c3
    ledivmul
    mp3an2
    mpanr12
    syl
    mpbird
    @9
    @52
    @38
    @56
    @57
    wa
    @58
    wi
    #
    @53
    @40
    @52
    @38
    wa
    @43
    @63
    @75
    2re
    1re
    @46
    @6
    c2
    c1
    le2add
    mpanr12
    syl2anc
    mp2and
    df-3
    syl6breqr
    @9
    @47
    c3
    @6
    @9
    @46
    @6
    @53
    @40
    readdcld
    @72
    @9
    3re
    a1i
    @27
    lemul1d
    mpbid
    @9
    @5
    cc
    wcel
    #
    @54
    @5
    wceq
    #
    @9
    @5
    @26
    recnd
    @76
    c3
    cc
    wcel
    c3
    cc0
    wne
    @77
    3cn
    3ne0
    @5
    c3
    divcan2
    mp3an23
    syl
    breqtrd
    eqbrtrd
    @9
    @3
    @31
    cA
    @42
    @9
    @29
    @30
    @44
    @45
    readdcld
    @68
    leaddsub2d
    mpbird
    eqbrtrd
    @10
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    @14
    vy
    @7
    crp
    cS
    @10
    @7
    wceq
    @78
    @13
    cA
    cle
    @10
    @7
    c2
    cexp
    oveq1
    breq1d
    cS
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    vx
    crp
    crab
    @79
    vy
    crp
    crab
    sqrlem1.1
    @82
    @79
    vx
    vy
    crp
    @80
    @10
    wceq
    @81
    @78
    cA
    cle
    @80
    @10
    c2
    cexp
    oveq1
    breq1d
    cbvrabv
    eqtri
    elrab2
    sylanbrc
    @11
    @12
    wa
    @7
    cS
    cr
    clt
    csup
    cB
    cle
    vy
    vz
    cS
    @7
    suprub
    sqrlem1.2
    syl6breqr
    syl2anc
    @2
    @4
    cc0
    @6
    clt
    wbr
    #
    @8
    wn
    #
    @9
    @6
    @27
    rpgt0d
    @2
    @83
    @84
    @2
    @83
    cB
    @7
    clt
    wbr
    @84
    @2
    @6
    cB
    @39
    @23
    ltaddposd
    @2
    cB
    @7
    @23
    @2
    cB
    @6
    @23
    @39
    readdcld
    ltnled
    bitrd
    biimpa
    syldan
    pm2.65da
    @2
    @3
    cA
    @24
    @21
    eqleltd
    mpbir2and
end
