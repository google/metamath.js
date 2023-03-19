include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "cioc.mm"
include "wo.mm"
include "cmul.mm"
include "cfv.mm"
include "cxad.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "0le1.mm"
include "snunioc.mm"
include "mp3an.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "elsni.mm"
include "orim1i.mm"
include "sylbi.mm"
include "wa.mm"
include "cpnf.mm"
include "0elunit.mm"
include "cv.mm"
include "clog.mm"
include "cneg.mm"
include "cif.mm"
include "iftrue.mm"
include "pnfex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "cmnf.mm"
include "wne.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "negeqd.mm"
include "ifbieq2d.mm"
include "negex.mm"
include "ifex.mm"
include "pnfxr.mm"
include "a1i.mm"
include "wn.mm"
include "cr.mm"
include "elunitrn.mm"
include "adantr.mm"
include "elunitge0.mm"
include "simpr.mm"
include "neqned.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "relogcld.mm"
include "renegcld.mm"
include "rexrd.mm"
include "ifclda.mm"
include "eqeltrd.mm"
include "neeq1.mm"
include "pnfnemnf.mm"
include "renemnfd.mm"
include "ifbothda.mm"
include "eqnetrd.mm"
include "xaddpnf1.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "cc.mm"
include "unitsscn.mm"
include "simpl.mm"
include "sseldi.mm"
include "mul01d.mm"
include "fveq2d.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "oveq1i.mm"
include "xrge0iifcv.mm"
include "crp.mm"
include "cioo.mm"
include "clt.mm"
include "wss.mm"
include "0le0.mm"
include "ltpnf.mm"
include "iocssioo.mm"
include "mp4an.mm"
include "ioorp.mm"
include "sseqtri.mm"
include "sseli.mm"
include "syl.mm"
include "xaddpnf2.mm"
include "rpssre.mm"
include "sstri.mm"
include "ax-resscn.mm"
include "mul02d.mm"
include "oveq1d.mm"
include "caddc.mm"
include "rexadd.mm"
include "oveqan12d.mm"
include "rpred.mm"
include "remulcld.mm"
include "rpgt0d.mm"
include "mulgt0d.mm"
include "iocssicc.mm"
include "iimulcl.mm"
include "0re.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "w3a.mm"
include "wb.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "relogmuld.mm"
include "recnd.mm"
include "negdid.mm"
include "3eqtrd.mm"
include "jaoian.mm"
include "sylan.mm"
include "jaodan.mm"
include "sylan2.mm"

theorem xrge0iifhom
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let vu: setvar u
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )
  assume xrge0iifhmeo.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  disjoint X x
  disjoint F x
  disjoint Y x
  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint u x
  assert |- ( ( X e. ( 0 [,] 1 ) /\ Y e. ( 0 [,] 1 ) ) -> ( F ` ( X x. Y ) ) = ( ( F ` X ) +e ( F ` Y ) ) )

  proof
    cY
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    cX
    @0
    wcel
    #
    cY
    cc0
    wceq
    #
    cY
    cc0
    c1
    cioc
    co
    #
    wcel
    #
    wo
    #
    cX
    cY
    cmul
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cxad
    co
    #
    wceq
    #
    @1
    cY
    cc0
    csn
    #
    wcel
    #
    @5
    wo
    #
    @6
    @1
    cY
    @13
    @4
    cun
    #
    wcel
    @15
    @16
    @0
    cY
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    cc0
    c1
    cle
    wbr
    @16
    @0
    wceq
    0xr
    c1
    1re
    rexri
    0le1
    cc0
    c1
    snunioc
    mp3an
    #
    eleq2i
    cY
    @13
    @4
    elun
    bitr3i
    @14
    @3
    @5
    cY
    cc0
    elsni
    orim1i
    sylbi
    @2
    @3
    @12
    @5
    @2
    @3
    wa
    #
    @9
    cc0
    cF
    cfv
    #
    cxad
    co
    #
    cX
    cc0
    cmul
    co
    #
    cF
    cfv
    #
    @11
    @8
    @19
    @21
    cpnf
    @23
    @19
    @21
    @9
    cpnf
    cxad
    co
    #
    cpnf
    @20
    cpnf
    @9
    cxad
    cc0
    @0
    wcel
    @20
    cpnf
    wceq
    0elunit
    vx
    cc0
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @25
    clog
    cfv
    #
    cneg
    #
    cif
    #
    cpnf
    @0
    cF
    @26
    cpnf
    @28
    iftrue
    xrge0iifhmeo.1
    pnfex
    fvmpt
    ax-mp
    #
    oveq2i
    @19
    @9
    cxr
    wcel
    #
    @9
    cmnf
    wne
    #
    @24
    cpnf
    wceq
    @2
    @31
    @3
    @2
    @9
    cX
    cc0
    wceq
    #
    cpnf
    cX
    clog
    cfv
    #
    cneg
    #
    cif
    #
    cxr
    vx
    cX
    @29
    @36
    @0
    cF
    @25
    cX
    wceq
    #
    @26
    @33
    @28
    @35
    cpnf
    @25
    cX
    cc0
    eqeq1
    @37
    @27
    @34
    @25
    cX
    clog
    fveq2
    negeqd
    ifbieq2d
    xrge0iifhmeo.1
    @33
    cpnf
    @35
    pnfex
    @34
    negex
    ifex
    fvmpt
    #
    @2
    @33
    cpnf
    @35
    cxr
    cpnf
    cxr
    wcel
    #
    @2
    @33
    wa
    #
    pnfxr
    a1i
    @2
    @33
    wn
    #
    wa
    #
    @35
    @42
    @34
    @42
    cX
    @42
    cX
    @2
    cX
    cr
    wcel
    @41
    cX
    elunitrn
    adantr
    #
    @42
    cX
    @43
    @2
    cc0
    cX
    cle
    wbr
    @41
    cX
    elunitge0
    adantr
    @42
    cX
    cc0
    @2
    @41
    simpr
    neqned
    ne0gt0d
    elrpd
    relogcld
    renegcld
    #
    rexrd
    ifclda
    eqeltrd
    adantr
    @2
    @32
    @3
    @2
    @9
    @36
    cmnf
    @38
    @33
    cpnf
    cmnf
    wne
    #
    @35
    cmnf
    wne
    @36
    cmnf
    wne
    @2
    cpnf
    @35
    cpnf
    @36
    cmnf
    neeq1
    @35
    @36
    cmnf
    neeq1
    @45
    @40
    pnfnemnf
    a1i
    @42
    @35
    @44
    renemnfd
    ifbothda
    eqnetrd
    adantr
    @9
    xaddpnf1
    syl2anc
    syl5eq
    @19
    @23
    @20
    cpnf
    @19
    @22
    cc0
    cF
    @19
    cX
    @19
    @0
    cc
    cX
    unitsscn
    @2
    @3
    simpl
    sseldi
    mul01d
    fveq2d
    @30
    syl6eq
    eqtr4d
    @19
    @10
    @20
    @9
    cxad
    @19
    cY
    cc0
    cF
    @2
    @3
    simpr
    #
    fveq2d
    oveq2d
    @19
    @7
    @22
    cF
    @19
    cY
    cc0
    cX
    cmul
    @46
    oveq2d
    fveq2d
    3eqtr4rd
    @2
    @33
    cX
    @4
    wcel
    #
    wo
    #
    @5
    @12
    @2
    cX
    @13
    wcel
    #
    @47
    wo
    #
    @48
    @2
    cX
    @16
    wcel
    @50
    @16
    @0
    cX
    @18
    eleq2i
    cX
    @13
    @4
    elun
    bitr3i
    @49
    @33
    @47
    cX
    cc0
    elsni
    orim1i
    sylbi
    @33
    @5
    @12
    @47
    @33
    @5
    wa
    #
    @20
    @10
    cxad
    co
    #
    cc0
    cY
    cmul
    co
    #
    cF
    cfv
    #
    @11
    @8
    @51
    @52
    cpnf
    @54
    @51
    @52
    cpnf
    @10
    cxad
    co
    #
    cpnf
    @20
    cpnf
    @10
    cxad
    @30
    oveq1i
    @51
    @10
    cxr
    wcel
    #
    @10
    cmnf
    wne
    #
    @55
    cpnf
    wceq
    @51
    @5
    @56
    @33
    @5
    simpr
    #
    @5
    @10
    @5
    @10
    cY
    clog
    cfv
    #
    cneg
    #
    cr
    vx
    cF
    cY
    xrge0iifhmeo.1
    xrge0iifcv
    #
    @5
    @59
    @5
    cY
    @4
    crp
    cY
    @4
    cc0
    cpnf
    cioo
    co
    #
    crp
    @17
    @39
    cc0
    cc0
    cle
    wbr
    c1
    cpnf
    clt
    wbr
    #
    @4
    @62
    wss
    0xr
    pnfxr
    0le0
    c1
    cr
    wcel
    #
    @63
    1re
    c1
    ltpnf
    ax-mp
    cc0
    cpnf
    cc0
    c1
    iocssioo
    mp4an
    ioorp
    sseqtri
    #
    sseli
    relogcld
    renegcld
    eqeltrd
    #
    rexrd
    syl
    @51
    @5
    @57
    @58
    @5
    @10
    @66
    renemnfd
    syl
    @10
    xaddpnf2
    syl2anc
    syl5eq
    @51
    @54
    @20
    cpnf
    @51
    @53
    cc0
    cF
    @51
    cY
    @51
    @4
    cc
    cY
    @4
    cr
    cc
    @4
    crp
    cr
    @65
    rpssre
    sstri
    ax-resscn
    sstri
    @58
    sseldi
    mul02d
    fveq2d
    @30
    syl6eq
    eqtr4d
    @51
    @9
    @20
    @10
    cxad
    @51
    cX
    cc0
    cF
    @33
    @5
    simpl
    #
    fveq2d
    oveq1d
    @51
    @7
    @53
    cF
    @51
    cX
    cc0
    cY
    cmul
    @67
    oveq1d
    fveq2d
    3eqtr4rd
    @47
    @5
    wa
    #
    @35
    @60
    cxad
    co
    #
    @35
    @60
    caddc
    co
    #
    @11
    @8
    @68
    @35
    cr
    wcel
    @60
    cr
    wcel
    @69
    @70
    wceq
    @68
    @34
    @68
    cX
    @68
    @4
    crp
    cX
    @65
    @47
    @5
    simpl
    #
    sseldi
    #
    relogcld
    #
    renegcld
    @68
    @59
    @68
    cY
    @68
    @4
    crp
    cY
    @65
    @47
    @5
    simpr
    #
    sseldi
    #
    relogcld
    #
    renegcld
    @35
    @60
    rexadd
    syl2anc
    @47
    @5
    @9
    @35
    @10
    @60
    cxad
    vx
    cF
    cX
    xrge0iifhmeo.1
    xrge0iifcv
    @61
    oveqan12d
    @68
    @8
    @7
    clog
    cfv
    #
    cneg
    #
    @34
    @59
    caddc
    co
    #
    cneg
    @70
    @68
    @7
    @4
    wcel
    #
    @8
    @78
    wceq
    @68
    @7
    cr
    wcel
    #
    cc0
    @7
    clt
    wbr
    #
    @7
    c1
    cle
    wbr
    #
    @80
    @68
    cX
    cY
    @68
    cX
    @72
    rpred
    #
    @68
    cY
    @75
    rpred
    #
    remulcld
    @68
    cX
    cY
    @84
    @85
    @68
    cX
    @72
    rpgt0d
    @68
    cY
    @75
    rpgt0d
    mulgt0d
    @68
    @7
    @0
    wcel
    #
    @83
    @68
    @2
    @1
    @86
    @68
    @4
    @0
    cX
    cc0
    c1
    iocssicc
    #
    @71
    sseldi
    @68
    @4
    @0
    cY
    @87
    @74
    sseldi
    cX
    cY
    iimulcl
    syl2anc
    @86
    @81
    cc0
    @7
    cle
    wbr
    @83
    cc0
    c1
    @7
    0re
    1re
    elicc2i
    simp3bi
    syl
    @17
    @64
    @80
    @81
    @82
    @83
    w3a
    wb
    0xr
    1re
    cc0
    c1
    @7
    elioc2
    mp2an
    syl3anbrc
    vx
    cF
    @7
    xrge0iifhmeo.1
    xrge0iifcv
    syl
    @68
    @77
    @79
    @68
    cX
    cY
    @72
    @75
    relogmuld
    negeqd
    @68
    @34
    @59
    @68
    @34
    @73
    recnd
    @68
    @59
    @76
    recnd
    negdid
    3eqtrd
    3eqtr4rd
    jaoian
    sylan
    jaodan
    sylan2
end
