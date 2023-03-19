include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "ineq12i.mm"
include "inrab.mm"
include "eqtri.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cgcd.mm"
include "cz.mm"
include "wi.mm"
include "cn0.mm"
include "odcl.mm"
include "adantl.mm"
include "nn0zd.mm"
include "nnzd.mm"
include "adantr.mm"
include "dvdsgcd.mm"
include "syl3anc.mm"
include "3impia.mm"
include "3ad2ant1.mm"
include "breqtrd.mm"
include "wb.mm"
include "simp2.mm"
include "dvds1.mm"
include "3syl.mm"
include "mpbid.mm"
include "cgrp.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "odeq1.mm"
include "syl2anc.mm"
include "velsn.mm"
include "sylibr.mm"
include "rabssdv.mm"
include "syl5eqss.mm"
include "csubg.mm"
include "oddvdssubg.mm"
include "syl5eqel.mm"
include "subg0cl.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"
include "wss.mm"
include "lsmsubg2.mm"
include "subgss.mm"
include "cmg.mm"
include "eqid.mm"
include "mulg1.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "bezout.mm"
include "ad2antrr.mm"
include "eqeq1d.mm"
include "cplusg.mm"
include "simprl.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "simprr.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "simplr.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "mulgcl.mm"
include "chash.mm"
include "cfn.mm"
include "nnmulcld.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "oddvds2.mm"
include "ad2antlr.mm"
include "dvdsmultr1.mm"
include "mpd.mm"
include "mulassd.mm"
include "odmulgid.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "mulass.mm"
include "mul12.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "rexlimdvva.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "jca.mm"

theorem ablfacrp
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.po: class .(+)
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  assume ablfacrp.b: |- B = ( Base ` G )
  assume ablfacrp.o: |- O = ( od ` G )
  assume ablfacrp.k: |- K = { x e. B | ( O ` x ) || M }
  assume ablfacrp.l: |- L = { x e. B | ( O ` x ) || N }
  assume ablfacrp.g: |- ( ph -> G e. Abel )
  assume ablfacrp.m: |- ( ph -> M e. NN )
  assume ablfacrp.n: |- ( ph -> N e. NN )
  assume ablfacrp.1: |- ( ph -> ( M gcd N ) = 1 )
  assume ablfacrp.2: |- ( ph -> ( # ` B ) = ( M x. N ) )
  assume ablfacrp.z: |- .0. = ( 0g ` G )
  assume ablfacrp.s: |- .(+) = ( LSSum ` G )

  disjoint B x
  disjoint G x
  disjoint O x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint .0. x
  disjoint a b
  disjoint a g
  disjoint a x
  disjoint B a
  disjoint b g
  disjoint b x
  disjoint B b
  disjoint g x
  disjoint B g
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint a p
  disjoint K a
  disjoint b p
  disjoint K b
  disjoint g p
  disjoint K g
  disjoint K p
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) g
  disjoint M a
  disjoint M b
  disjoint M g
  disjoint N a
  disjoint N b
  disjoint p x
  disjoint N p
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint p ph
  assert |- ( ph -> ( ( K i^i L ) = { .0. } /\ ( K .(+) L ) = B ) )

  proof
    wph
    cK
    cL
    cin
    #
    c.0
    csn
    #
    wceq
    cK
    cL
    c.po
    co
    #
    cB
    wceq
    wph
    @0
    @1
    wph
    @0
    vx
    cv
    #
    cO
    cfv
    #
    cM
    cdvds
    wbr
    #
    @4
    cN
    cdvds
    wbr
    #
    wa
    #
    vx
    cB
    crab
    #
    @1
    @0
    @5
    vx
    cB
    crab
    #
    @6
    vx
    cB
    crab
    #
    cin
    @8
    cK
    @9
    cL
    @10
    ablfacrp.k
    ablfacrp.l
    ineq12i
    @5
    @6
    vx
    cB
    inrab
    eqtri
    wph
    @7
    vx
    cB
    @1
    wph
    @3
    cB
    wcel
    #
    @7
    w3a
    #
    @3
    c.0
    wceq
    #
    @3
    @1
    wcel
    @12
    @4
    c1
    wceq
    #
    @13
    @12
    @4
    c1
    cdvds
    wbr
    #
    @14
    @12
    @4
    cM
    cN
    cgcd
    co
    #
    c1
    cdvds
    wph
    @11
    @7
    @4
    @16
    cdvds
    wbr
    #
    wph
    @11
    wa
    #
    @4
    cz
    wcel
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @7
    @17
    wi
    @18
    @4
    @11
    @4
    cn0
    wcel
    #
    wph
    @3
    cG
    cO
    cB
    ablfacrp.b
    ablfacrp.o
    odcl
    #
    adantl
    nn0zd
    wph
    @19
    @11
    wph
    cM
    ablfacrp.m
    nnzd
    #
    adantr
    wph
    @20
    @11
    wph
    cN
    ablfacrp.n
    nnzd
    #
    adantr
    @4
    cM
    cN
    dvdsgcd
    syl3anc
    3impia
    wph
    @11
    @16
    c1
    wceq
    #
    @7
    ablfacrp.1
    3ad2ant1
    breqtrd
    @12
    @11
    @21
    @15
    @14
    wb
    wph
    @11
    @7
    simp2
    #
    @22
    @4
    dvds1
    3syl
    mpbid
    @12
    cG
    cgrp
    wcel
    #
    @11
    @14
    @13
    wb
    wph
    @11
    @27
    @7
    wph
    cG
    cabl
    wcel
    #
    @27
    ablfacrp.g
    cG
    ablgrp
    syl
    #
    3ad2ant1
    @26
    @3
    cG
    cO
    cB
    c.0
    ablfacrp.o
    ablfacrp.z
    ablfacrp.b
    odeq1
    syl2anc
    mpbid
    vx
    c.0
    velsn
    sylibr
    rabssdv
    syl5eqss
    wph
    c.0
    @0
    wph
    cK
    cL
    c.0
    wph
    cK
    cG
    csubg
    cfv
    #
    wcel
    #
    c.0
    cK
    wcel
    wph
    cK
    @9
    @30
    ablfacrp.k
    wph
    @28
    @19
    @9
    @30
    wcel
    ablfacrp.g
    @23
    vx
    cB
    cG
    cM
    cO
    ablfacrp.o
    ablfacrp.b
    oddvdssubg
    syl2anc
    syl5eqel
    #
    cK
    cG
    c.0
    ablfacrp.z
    subg0cl
    syl
    wph
    cL
    @30
    wcel
    #
    c.0
    cL
    wcel
    wph
    cL
    @10
    @30
    ablfacrp.l
    wph
    @28
    @20
    @10
    @30
    wcel
    ablfacrp.g
    @24
    vx
    cB
    cG
    cN
    cO
    ablfacrp.o
    ablfacrp.b
    oddvdssubg
    syl2anc
    syl5eqel
    #
    cL
    cG
    c.0
    ablfacrp.z
    subg0cl
    syl
    elind
    snssd
    eqssd
    wph
    @2
    cB
    wph
    @2
    @30
    wcel
    #
    @2
    cB
    wss
    wph
    @28
    @31
    @33
    @35
    ablfacrp.g
    @32
    @34
    c.po
    cK
    cL
    cG
    ablfacrp.s
    lsmsubg2
    syl3anc
    cB
    @2
    cG
    ablfacrp.b
    subgss
    syl
    wph
    vg
    cB
    @2
    wph
    vg
    cv
    #
    cB
    wcel
    #
    @36
    @2
    wcel
    wph
    @37
    wa
    #
    c1
    @36
    cG
    cmg
    cfv
    #
    co
    #
    @36
    @2
    @37
    @40
    @36
    wceq
    wph
    cB
    @39
    cG
    @36
    ablfacrp.b
    @39
    eqid
    #
    mulg1
    adantl
    @38
    @16
    cM
    va
    cv
    #
    cmul
    co
    #
    cN
    vb
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
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @40
    @2
    wcel
    #
    wph
    @48
    @37
    wph
    @19
    @20
    @48
    @23
    @24
    va
    vb
    cM
    cN
    bezout
    syl2anc
    adantr
    @38
    @47
    @49
    va
    vb
    cz
    cz
    @38
    @42
    cz
    wcel
    #
    @44
    cz
    wcel
    #
    wa
    #
    wa
    #
    @47
    c1
    @46
    wceq
    #
    @49
    @53
    @16
    c1
    @46
    wph
    @25
    @37
    @52
    ablfacrp.1
    ad2antrr
    eqeq1d
    @53
    @49
    @54
    @46
    @36
    @39
    co
    #
    @2
    wcel
    @53
    @55
    @45
    @36
    @39
    co
    #
    @43
    @36
    @39
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    @53
    @55
    @45
    @43
    caddc
    co
    #
    @36
    @39
    co
    #
    @59
    @53
    @46
    @60
    @36
    @39
    @53
    @43
    @45
    @53
    @43
    @53
    cM
    @42
    wph
    @19
    @37
    @52
    @23
    ad2antrr
    #
    @38
    @50
    @51
    simprl
    #
    zmulcld
    #
    zcnd
    @53
    @45
    @53
    cN
    @44
    wph
    @20
    @37
    @52
    @24
    ad2antrr
    #
    @38
    @50
    @51
    simprr
    #
    zmulcld
    #
    zcnd
    addcomd
    oveq1d
    @53
    @27
    @45
    cz
    wcel
    #
    @43
    cz
    wcel
    #
    @37
    @61
    @59
    wceq
    wph
    @27
    @37
    @52
    @29
    ad2antrr
    #
    @67
    @64
    wph
    @37
    @52
    simplr
    #
    cB
    @58
    @39
    cG
    @45
    @43
    @36
    ablfacrp.b
    @41
    @58
    eqid
    #
    mulgdir
    syl13anc
    eqtrd
    @53
    @31
    @33
    @56
    cK
    wcel
    #
    @57
    cL
    wcel
    #
    @59
    @2
    wcel
    wph
    @31
    @37
    @52
    @32
    ad2antrr
    wph
    @33
    @37
    @52
    @34
    ad2antrr
    @53
    @56
    cB
    wcel
    #
    @56
    cO
    cfv
    #
    cM
    cdvds
    wbr
    #
    @73
    @53
    @27
    @68
    @37
    @75
    @70
    @67
    @71
    cB
    @39
    cG
    @45
    @36
    ablfacrp.b
    @41
    mulgcl
    syl3anc
    @53
    @77
    @36
    cO
    cfv
    #
    cM
    @45
    cmul
    co
    #
    cdvds
    wbr
    #
    @53
    @78
    cM
    cN
    cmul
    co
    #
    @44
    cmul
    co
    #
    @79
    cdvds
    @53
    @78
    @81
    cdvds
    wbr
    #
    @78
    @82
    cdvds
    wbr
    #
    @53
    @78
    cB
    chash
    cfv
    #
    @81
    cdvds
    @53
    @27
    cB
    cfn
    wcel
    #
    @37
    @78
    @85
    cdvds
    wbr
    @70
    wph
    @86
    @37
    @52
    wph
    @85
    cn0
    wcel
    #
    @86
    wph
    @85
    @81
    cn0
    ablfacrp.2
    wph
    @81
    wph
    cM
    cN
    ablfacrp.m
    ablfacrp.n
    nnmulcld
    nnnn0d
    eqeltrd
    cB
    cvv
    wcel
    @86
    @87
    wb
    cB
    cG
    cbs
    cfv
    cvv
    ablfacrp.b
    cG
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashclb
    ax-mp
    sylibr
    ad2antrr
    @71
    @36
    cG
    cO
    cB
    ablfacrp.b
    ablfacrp.o
    oddvds2
    syl3anc
    wph
    @85
    @81
    wceq
    @37
    @52
    ablfacrp.2
    ad2antrr
    breqtrd
    #
    @53
    @78
    cz
    wcel
    #
    @81
    cz
    wcel
    #
    @51
    @83
    @84
    wi
    @53
    @78
    @37
    @78
    cn0
    wcel
    wph
    @52
    @36
    cG
    cO
    cB
    ablfacrp.b
    ablfacrp.o
    odcl
    ad2antlr
    nn0zd
    #
    @53
    cM
    cN
    @62
    @65
    zmulcld
    #
    @66
    @78
    @81
    @44
    dvdsmultr1
    syl3anc
    mpd
    @53
    cM
    cN
    @44
    @53
    cM
    @62
    zcnd
    #
    @53
    cN
    @65
    zcnd
    #
    @53
    @44
    @66
    zcnd
    mulassd
    breqtrd
    @53
    @27
    @37
    @68
    @19
    @77
    @80
    wb
    @70
    @71
    @67
    @62
    @36
    @39
    cG
    cM
    @45
    cO
    cB
    ablfacrp.b
    ablfacrp.o
    @41
    odmulgid
    syl31anc
    mpbird
    @5
    @77
    vx
    @56
    cB
    cK
    @3
    @56
    wceq
    @4
    @76
    cM
    cdvds
    @3
    @56
    cO
    fveq2
    breq1d
    ablfacrp.k
    elrab2
    sylanbrc
    @53
    @57
    cB
    wcel
    #
    @57
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    @74
    @53
    @27
    @69
    @37
    @95
    @70
    @64
    @71
    cB
    @39
    cG
    @43
    @36
    ablfacrp.b
    @41
    mulgcl
    syl3anc
    @53
    @97
    @78
    cN
    @43
    cmul
    co
    #
    cdvds
    wbr
    #
    @53
    @78
    @81
    @42
    cmul
    co
    #
    @98
    cdvds
    @53
    @83
    @78
    @100
    cdvds
    wbr
    #
    @88
    @53
    @89
    @90
    @50
    @83
    @101
    wi
    @91
    @92
    @63
    @78
    @81
    @42
    dvdsmultr1
    syl3anc
    mpd
    @53
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @42
    cc
    wcel
    #
    @100
    @98
    wceq
    @93
    @94
    @50
    @104
    @38
    @51
    @42
    zcn
    ad2antrl
    @102
    @103
    @104
    w3a
    @100
    cM
    cN
    @42
    cmul
    co
    cmul
    co
    @98
    cM
    cN
    @42
    mulass
    cM
    cN
    @42
    mul12
    eqtrd
    syl3anc
    breqtrd
    @53
    @27
    @37
    @69
    @20
    @97
    @99
    wb
    @70
    @71
    @64
    @65
    @36
    @39
    cG
    cN
    @43
    cO
    cB
    ablfacrp.b
    ablfacrp.o
    @41
    odmulgid
    syl31anc
    mpbird
    @6
    @97
    vx
    @57
    cB
    cL
    @3
    @57
    wceq
    @4
    @96
    cN
    cdvds
    @3
    @57
    cO
    fveq2
    breq1d
    ablfacrp.l
    elrab2
    sylanbrc
    @58
    c.po
    cK
    cL
    cG
    @56
    @57
    @72
    ablfacrp.s
    lsmelvali
    syl22anc
    eqeltrd
    @54
    @40
    @55
    @2
    c1
    @46
    @36
    @39
    oveq1
    eleq1d
    syl5ibrcom
    sylbid
    rexlimdvva
    mpd
    eqeltrrd
    ex
    ssrdv
    eqssd
    jca
end
