include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cbl.mm"
include "wss.mm"
include "crp.mm"
include "cpt.mm"
include "fzfi.mm"
include "ctop.mm"
include "retop.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "ptval.mm"
include "mp2an.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "tg2.mm"
include "wi.mm"
include "elpt.mm"
include "fvex.mm"
include "fvconst2.mm"
include "eleq2d.mm"
include "ralbiia.mm"
include "cvv.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "r19.26.mm"
include "wf.mm"
include "cr.mm"
include "uniretop.mm"
include "eltopss.mm"
include "mpan.mm"
include "sselda.mm"
include "cxmt.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "r19.42v.mm"
include "sylanbrc.mm"
include "ralimi.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "ac6sfi.mm"
include "sylancr.mm"
include "c0.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "1rp.mm"
include "a1i.mm"
include "wn.mm"
include "frn.mm"
include "adantr.mm"
include "wne.mm"
include "ffn.mm"
include "fnfi.mm"
include "sylancl.mm"
include "rnfi.mm"
include "syl.mm"
include "cdm.mm"
include "dm0rn0.mm"
include "fdm.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "necon3abid.mm"
include "biimpar.mm"
include "rpssre.mm"
include "syl6ss.mm"
include "wor.mm"
include "ltso.mm"
include "fiinfcl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "ifclda.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rpxrd.mm"
include "ffvelrn.mm"
include "ne0i.mm"
include "ifnefalse.mm"
include "adantl.mm"
include "cc0.mm"
include "0re.mm"
include "rpge0.mm"
include "rgen.mm"
include "ssralv.mm"
include "mpisyl.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "infrelb.mm"
include "eqbrtrd.mm"
include "jca31.mm"
include "ssbl.mm"
include "3expb.mm"
include "mpanl1.mm"
include "ancoms.mm"
include "sstr2.mm"
include "expimpd.mm"
include "ralimdva.mm"
include "imp.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cres.mm"
include "fveq2i.mm"
include "oveqi.mm"
include "sseq1i.mm"
include "ralbii.mm"
include "nfv.mm"
include "nfxfr.mm"
include "rspce.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "sylbir.mm"
include "sylan2.mm"
include "sylanb.mm"
include "ss2ixp.mm"
include "syl11.mm"
include "reximdv.mm"
include "syl5com.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "rexlimiv.mm"

theorem ptrecube
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ptrecube.r: |- R = ( Xt_ ` ( ( 1 ... N ) X. { ( topGen ` ran (,) ) } ) )
  assume ptrecube.d: |- D = ( ( abs o. - ) |` ( RR X. RR ) )

  disjoint d n
  disjoint N d
  disjoint N n
  disjoint P d
  disjoint P n
  disjoint S d
  disjoint S n
  disjoint d g
  disjoint d h
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint g h
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint N g
  disjoint h n
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint N h
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint N w
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint P g
  disjoint P h
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S g
  disjoint S h
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D g
  disjoint D h
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R g
  disjoint R h
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( S e. R /\ P e. S ) -> E. d e. RR+ X_ n e. ( 1 ... N ) ( ( P ` n ) ( ball ` D ) d ) C_ S )

  proof
    cS
    cR
    wcel
    cS
    vh
    cv
    #
    c1
    cN
    cfz
    co
    #
    wfn
    #
    vn
    cv
    #
    @0
    cfv
    #
    @3
    @1
    cioo
    crn
    #
    ctg
    cfv
    #
    csn
    cxp
    #
    cfv
    #
    wcel
    vn
    @1
    wral
    @4
    @8
    cuni
    #
    wceq
    vn
    @1
    vw
    cv
    cdif
    wral
    vw
    cfn
    wrex
    w3a
    vx
    cv
    #
    vn
    @1
    @4
    cixp
    wceq
    wa
    vh
    wex
    vx
    cab
    #
    ctg
    cfv
    #
    wcel
    #
    cP
    cS
    wcel
    #
    vn
    @1
    @3
    cP
    cfv
    #
    vd
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cixp
    #
    cS
    wss
    #
    vd
    crp
    wrex
    #
    cR
    @12
    cS
    cR
    @7
    cpt
    cfv
    #
    @12
    ptrecube.r
    @1
    cfn
    wcel
    #
    @7
    @1
    wfn
    #
    @22
    @12
    wceq
    c1
    cN
    fzfi
    #
    @6
    ctop
    wcel
    #
    @24
    retop
    @1
    @6
    ctop
    fnconstg
    ax-mp
    vx
    vn
    vw
    @1
    @11
    vh
    @7
    cfn
    @11
    eqid
    #
    ptval
    mp2an
    eqtri
    eleq2i
    @13
    @14
    wa
    cP
    vz
    cv
    #
    wcel
    #
    @28
    cS
    wss
    #
    wa
    #
    vz
    @11
    wrex
    @21
    vz
    cS
    @11
    cP
    tg2
    @31
    @21
    vz
    @11
    @28
    @11
    wcel
    vg
    cv
    #
    @1
    wfn
    #
    @3
    @32
    cfv
    #
    @8
    wcel
    #
    vn
    @1
    wral
    #
    @34
    @9
    wceq
    vn
    @1
    @28
    cdif
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    @28
    vn
    @1
    @34
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    @31
    @21
    wi
    #
    vx
    vn
    vw
    vz
    @1
    @11
    @28
    vh
    vg
    @7
    @27
    elpt
    @41
    @42
    vg
    @38
    @40
    @42
    @36
    @33
    @40
    @42
    wi
    @37
    @36
    @42
    @40
    cP
    @39
    wcel
    #
    @39
    cS
    wss
    #
    wa
    #
    @21
    wi
    @36
    @43
    @44
    @21
    @36
    @43
    wa
    @18
    @34
    wss
    #
    vn
    @1
    wral
    #
    vd
    crp
    wrex
    #
    @44
    @21
    @36
    @34
    @6
    wcel
    #
    vn
    @1
    wral
    #
    @43
    @48
    @35
    @49
    vn
    @1
    @3
    @1
    wcel
    #
    @8
    @6
    @34
    @1
    @6
    @3
    @5
    ctg
    fvex
    fvconst2
    eleq2d
    ralbiia
    @43
    @50
    @15
    @34
    wcel
    #
    vn
    @1
    wral
    #
    @48
    @43
    cP
    cvv
    wcel
    cP
    @1
    wfn
    @53
    vn
    @1
    @34
    cP
    elixp2
    simp3bi
    @50
    @53
    wa
    @49
    @52
    wa
    #
    vn
    @1
    wral
    #
    @48
    @49
    @52
    vn
    @1
    r19.26
    @55
    @1
    crp
    @0
    wf
    #
    @15
    cr
    wcel
    #
    @15
    @4
    @17
    co
    #
    @34
    wss
    #
    wa
    #
    vn
    @1
    wral
    #
    wa
    #
    vh
    wex
    #
    @48
    @55
    @23
    @57
    @15
    vy
    cv
    #
    @17
    co
    #
    @34
    wss
    #
    wa
    #
    vy
    crp
    wrex
    #
    vn
    @1
    wral
    @63
    @25
    @54
    @68
    vn
    @1
    @54
    @57
    @66
    vy
    crp
    wrex
    #
    @68
    @49
    @34
    cr
    @15
    @26
    @49
    @34
    cr
    wss
    retop
    @34
    @6
    cr
    uniretop
    eltopss
    mpan
    sselda
    cD
    cr
    cxmt
    cfv
    wcel
    #
    @49
    @52
    @69
    cD
    ptrecube.d
    rexmet
    #
    vy
    @34
    cD
    @15
    @6
    cr
    cD
    cD
    cmopn
    cfv
    #
    ptrecube.d
    @72
    eqid
    tgioo
    mopni2
    mp3an1
    @57
    @66
    vy
    crp
    r19.42v
    sylanbrc
    ralimi
    @67
    @60
    vn
    vy
    @1
    crp
    vh
    @64
    @4
    wceq
    #
    @66
    @59
    @57
    @73
    @65
    @58
    @34
    @64
    @4
    @15
    @17
    oveq2
    sseq1d
    anbi2d
    ac6sfi
    sylancr
    @62
    @48
    vh
    @62
    @1
    c0
    wceq
    #
    c1
    @0
    crn
    #
    cr
    clt
    cinf
    #
    cif
    #
    crp
    wcel
    #
    @15
    @77
    @17
    co
    #
    @34
    wss
    #
    vn
    @1
    wral
    #
    @48
    @56
    @78
    @61
    @56
    @74
    c1
    @76
    crp
    c1
    crp
    wcel
    @56
    @74
    wa
    1rp
    a1i
    @56
    @74
    wn
    #
    wa
    #
    @75
    crp
    @76
    @56
    @75
    crp
    wss
    #
    @82
    @1
    crp
    @0
    frn
    #
    adantr
    @83
    @75
    cfn
    wcel
    #
    @75
    c0
    wne
    #
    @75
    cr
    wss
    #
    @76
    @75
    wcel
    #
    @56
    @86
    @82
    @56
    @0
    cfn
    wcel
    #
    @86
    @56
    @2
    @23
    @90
    @1
    crp
    @0
    ffn
    #
    @25
    @1
    @0
    fnfi
    sylancl
    @0
    rnfi
    syl
    adantr
    @56
    @87
    @82
    @56
    @74
    @75
    c0
    @75
    c0
    wceq
    @0
    cdm
    #
    c0
    wceq
    @56
    @74
    @0
    dm0rn0
    @56
    @92
    @1
    c0
    @1
    crp
    @0
    fdm
    eqeq1d
    syl5bbr
    necon3abid
    biimpar
    @56
    @88
    @82
    @56
    @75
    crp
    cr
    @85
    rpssre
    syl6ss
    #
    adantr
    cr
    clt
    wor
    @86
    @87
    @88
    w3a
    @89
    ltso
    cr
    @75
    clt
    fiinfcl
    mpan
    syl3anc
    sseldd
    ifclda
    #
    adantr
    @56
    @61
    @81
    @56
    @60
    @80
    vn
    @1
    @56
    @51
    wa
    #
    @57
    @59
    @80
    @95
    @57
    wa
    @79
    @58
    wss
    #
    @59
    @80
    wi
    @95
    @77
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    wa
    #
    @77
    @4
    cle
    wbr
    #
    wa
    #
    @57
    @96
    @95
    @97
    @98
    @100
    @95
    @77
    @56
    @78
    @51
    @94
    adantr
    rpxrd
    @95
    @4
    @1
    crp
    @3
    @0
    ffvelrn
    rpxrd
    @95
    @77
    @76
    @4
    cle
    @51
    @77
    @76
    wceq
    #
    @56
    @51
    @1
    c0
    wne
    @102
    @1
    @3
    ne0i
    @1
    c0
    c1
    @76
    ifnefalse
    syl
    adantl
    @95
    @88
    @10
    @64
    cle
    wbr
    #
    vy
    @75
    wral
    #
    vx
    cr
    wrex
    #
    @4
    @75
    wcel
    #
    @76
    @4
    cle
    wbr
    @56
    @88
    @51
    @93
    adantr
    @56
    @105
    @51
    @56
    cc0
    cr
    wcel
    cc0
    @64
    cle
    wbr
    #
    vy
    @75
    wral
    #
    @105
    0re
    @56
    @84
    @107
    vy
    crp
    wral
    @108
    @85
    @107
    vy
    crp
    @64
    rpge0
    rgen
    @107
    vy
    @75
    crp
    ssralv
    mpisyl
    @104
    @108
    vx
    cc0
    cr
    @10
    cc0
    wceq
    @103
    @107
    vy
    @75
    @10
    cc0
    @64
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    adantr
    @56
    @2
    @51
    @106
    @91
    @1
    @3
    @0
    fnfvelrn
    sylan
    vx
    vy
    @4
    @75
    infrelb
    syl3anc
    eqbrtrd
    jca31
    @57
    @101
    @96
    @70
    @57
    @101
    @96
    @71
    @70
    @57
    wa
    @99
    @100
    @96
    cD
    @15
    @77
    @4
    cr
    ssbl
    3expb
    mpanl1
    ancoms
    sylan
    @79
    @58
    @34
    sstr2
    syl
    expimpd
    ralimdva
    imp
    @47
    @81
    vd
    @77
    crp
    @81
    @15
    @77
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    #
    co
    #
    @34
    wss
    #
    vn
    @1
    wral
    #
    vd
    @80
    @112
    vn
    @1
    @79
    @111
    @34
    @17
    @110
    @15
    @77
    cD
    @109
    cbl
    ptrecube.d
    fveq2i
    oveqi
    sseq1i
    ralbii
    @113
    vd
    nfv
    nfxfr
    @16
    @77
    wceq
    #
    @46
    @80
    vn
    @1
    @114
    @18
    @79
    @34
    @16
    @77
    @15
    @17
    oveq2
    sseq1d
    ralbidv
    rspce
    syl2anc
    exlimiv
    syl
    sylbir
    sylan2
    sylanb
    @44
    @47
    @20
    vd
    crp
    @19
    @39
    wss
    @44
    @20
    @47
    @19
    @39
    cS
    sstr2
    vn
    @1
    @18
    @34
    ss2ixp
    syl11
    reximdv
    syl5com
    expimpd
    @40
    @31
    @45
    @21
    @40
    @29
    @43
    @30
    @44
    @28
    @39
    cP
    eleq2
    @28
    @39
    cS
    sseq1
    anbi12d
    imbi1d
    syl5ibrcom
    3ad2ant2
    imp
    exlimiv
    sylbi
    rexlimiv
    syl
    sylanb
end
