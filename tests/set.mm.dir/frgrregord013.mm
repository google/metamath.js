include "cfn.mm"
include "wcel.mm"
include "cfrgr.mm"
include "crusgr.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "c3.mm"
include "w3o.mm"
include "cn0.mm"
include "wi.mm"
include "hashcl.mm"
include "w3a.mm"
include "wa.mm"
include "ax-1.mm"
include "wn.mm"
include "3ioran.mm"
include "wne.mm"
include "df-ne.mm"
include "c0.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "cn.mm"
include "elnnne0.mm"
include "c2.mm"
include "cuz.mm"
include "eluz2b3.mm"
include "cv.mm"
include "cpr.mm"
include "wex.mm"
include "hash2prde.mm"
include "wnel.mm"
include "cvv.mm"
include "cvtx.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "3jca.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "nfrgr2v.mm"
include "syl2an.mm"
include "df-nel.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "com23.mm"
include "exlimivv.mm"
include "syl.mm"
include "ex.mm"
include "com14.mm"
include "3imp.mm"
include "com12.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "cvtxdg.mm"
include "wral.mm"
include "eqid.mm"
include "rusgrprop0.mm"
include "clt.mm"
include "eluz2gt1.mm"
include "anim2i.mm"
include "ancoms.mm"
include "vdgn0frgrv2.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "eqeq2.mm"
include "ralbidv.mm"
include "r19.26.mm"
include "wfal.mm"
include "nne.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "ancom.mm"
include "pm3.24.mm"
include "bifal.mm"
include "3bitri.mm"
include "ralbii.mm"
include "r19.3rzv.mm"
include "falim.mm"
include "syl6bir.mm"
include "adantl.mm"
include "sylbi.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "com4t.mm"
include "3syl.mm"
include "com25.mm"
include "com15.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "frrusgrord.mm"
include "imp.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "2t1e2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "2p1e3.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "pm2.21.mm"
include "ad2antrr.mm"
include "syl5com.mm"
include "wo.mm"
include "frgrreg.mm"
include "mpjaod.mm"
include "exp32.mm"
include "com34.mm"
include "exp4c.mm"
include "com3r.mm"
include "pm2.61i.mm"
include "3exp.mm"
include "syl5bir.mm"
include "impd.mm"
include "mpcom.mm"
include "com24.mm"
include "3exp1.mm"
include "3imp21.mm"

theorem frgrregord013
  let cG: class G
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  assume frgrreggt1.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ V e. Fin /\ G RegUSGraph K ) -> ( ( # ` V ) = 0 \/ ( # ` V ) = 1 \/ ( # ` V ) = 3 ) )

  proof
    cV
    cfn
    wcel
    #
    cG
    cfrgr
    wcel
    #
    cG
    cK
    crusgr
    wbr
    #
    cV
    chash
    cfv
    #
    cc0
    wceq
    #
    @3
    c1
    wceq
    #
    @3
    c3
    wceq
    #
    w3o
    #
    @3
    cn0
    wcel
    #
    @0
    @1
    @2
    @7
    wi
    #
    wi
    #
    cV
    hashcl
    @8
    @0
    @1
    @2
    @7
    @7
    @8
    @0
    @1
    w3a
    #
    @2
    wa
    #
    @7
    wi
    #
    @7
    @12
    ax-1
    @7
    wn
    @4
    wn
    #
    @5
    wn
    #
    @6
    wn
    #
    w3a
    @13
    @4
    @5
    @6
    3ioran
    @14
    @15
    @16
    @13
    @12
    @15
    @16
    @14
    @7
    @11
    @2
    @15
    @16
    @14
    @7
    wi
    wi
    wi
    @11
    @14
    @15
    @16
    @2
    @7
    @8
    @0
    @1
    @14
    @15
    @16
    @9
    wi
    #
    wi
    #
    wi
    @8
    @14
    @1
    @0
    @18
    @14
    @3
    cc0
    wne
    #
    @8
    @1
    @0
    @18
    wi
    wi
    @3
    cc0
    df-ne
    @0
    @19
    @1
    @8
    @18
    @0
    @19
    @1
    @8
    @18
    wi
    wi
    #
    cV
    c0
    wne
    #
    @0
    @19
    wa
    #
    @20
    @0
    @19
    @21
    @0
    @3
    cc0
    cV
    c0
    cV
    cfn
    hasheq0
    necon3bid
    biimpa
    @8
    @22
    @1
    @21
    @18
    @8
    @0
    @19
    @1
    @21
    @18
    wi
    wi
    #
    @8
    @19
    @0
    @23
    @8
    @19
    @0
    @23
    wi
    #
    @8
    @19
    wa
    @3
    cn
    wcel
    #
    @24
    @3
    elnnne0
    @25
    @15
    @1
    @21
    @0
    @17
    @15
    @3
    c1
    wne
    #
    @25
    @1
    @21
    @0
    @17
    wi
    #
    wi
    wi
    #
    @3
    c1
    df-ne
    @25
    @26
    @28
    @25
    @26
    wa
    @3
    c2
    cuz
    cfv
    wcel
    #
    @28
    @3
    eluz2b3
    @29
    @1
    @21
    @27
    @3
    c2
    wceq
    #
    @29
    @1
    @21
    w3a
    #
    @27
    wi
    @31
    @30
    @27
    @29
    @1
    @21
    @30
    @27
    wi
    #
    @1
    @21
    @32
    wi
    wi
    @29
    @0
    @21
    @30
    @1
    @17
    @0
    @30
    @21
    @1
    @17
    wi
    #
    @0
    @30
    @21
    @33
    wi
    #
    @0
    @30
    wa
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cV
    @35
    @36
    cpr
    #
    wceq
    #
    wa
    #
    vb
    wex
    va
    wex
    @34
    cV
    cfn
    va
    vb
    hash2prde
    @40
    @34
    va
    vb
    @40
    @1
    @21
    @17
    @40
    @1
    @21
    @17
    wi
    @40
    cG
    cfrgr
    wnel
    #
    @1
    wn
    @37
    @35
    cvv
    wcel
    #
    @36
    cvv
    wcel
    #
    @37
    w3a
    cG
    cvtx
    cfv
    #
    @38
    wceq
    #
    @41
    @39
    @37
    @42
    @43
    @37
    @42
    @37
    va
    vex
    a1i
    @43
    @37
    vb
    vex
    a1i
    @37
    id
    3jca
    @39
    @45
    cV
    @44
    @38
    frgrreggt1.v
    eqeq1i
    biimpi
    @35
    @36
    cG
    cvv
    cvv
    nfrgr2v
    syl2an
    cG
    cfrgr
    df-nel
    sylib
    pm2.21d
    com23
    exlimivv
    syl
    ex
    com23
    com14
    a1i
    3imp
    com12
    @31
    @0
    @30
    wn
    #
    @17
    @29
    @1
    @21
    @0
    @46
    @17
    wi
    #
    wi
    @0
    @1
    @21
    @29
    @47
    @0
    @21
    @1
    @29
    @47
    wi
    #
    @0
    @21
    @1
    @48
    wi
    @0
    @21
    wa
    #
    @16
    @29
    @46
    @1
    @9
    @49
    @16
    @46
    @29
    @10
    @49
    @16
    @46
    @29
    @10
    @49
    @1
    @16
    @46
    wa
    #
    @29
    wa
    #
    @9
    @49
    @1
    @2
    @51
    @7
    @49
    @1
    @2
    @51
    @7
    wi
    #
    @49
    @1
    @2
    wa
    #
    wa
    #
    cK
    cc0
    wceq
    #
    @52
    cK
    c2
    wceq
    #
    @53
    @49
    @55
    @52
    wi
    #
    @2
    @1
    @49
    @57
    wi
    #
    @2
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    @1
    @58
    wi
    #
    vv
    @62
    cG
    cK
    cV
    frgrreggt1.v
    @62
    eqid
    rusgrprop0
    @65
    @59
    @66
    @60
    @1
    @65
    @58
    @51
    @65
    @49
    @55
    @1
    @7
    @29
    @65
    @49
    @55
    @1
    @7
    wi
    wi
    wi
    wi
    @50
    @29
    @1
    @49
    @55
    @65
    @7
    @29
    @1
    @49
    @55
    @65
    @7
    wi
    wi
    wi
    #
    @29
    @1
    wa
    @1
    c1
    @3
    clt
    wbr
    #
    wa
    #
    @63
    cc0
    wne
    #
    vv
    cV
    wral
    #
    @67
    @1
    @29
    @69
    @29
    @68
    @1
    @3
    eluz2gt1
    anim2i
    ancoms
    @69
    @70
    vv
    cV
    @1
    @61
    cV
    wcel
    @68
    @70
    cG
    @61
    cV
    frgrreggt1.v
    vdgn0frgrv2
    impancom
    ralrimiv
    @55
    @65
    @71
    @49
    @7
    @55
    @65
    @63
    cc0
    wceq
    #
    vv
    cV
    wral
    #
    @71
    @49
    @7
    wi
    #
    wi
    @55
    @64
    @72
    vv
    cV
    cK
    cc0
    @63
    eqeq2
    ralbidv
    @73
    @71
    @74
    @73
    @71
    wa
    @72
    @70
    wa
    #
    vv
    cV
    wral
    #
    @74
    @72
    @70
    vv
    cV
    r19.26
    @76
    wfal
    vv
    cV
    wral
    #
    @74
    @75
    wfal
    vv
    cV
    @75
    @70
    wn
    #
    @70
    wa
    @70
    @78
    wa
    #
    wfal
    @72
    @78
    @70
    @78
    @72
    @63
    cc0
    nne
    bicomi
    anbi1i
    @78
    @70
    ancom
    @79
    @70
    pm3.24
    bifal
    3bitri
    ralbii
    @49
    @77
    @7
    @21
    @77
    @7
    wi
    @0
    @21
    @77
    wfal
    @7
    wfal
    vv
    cV
    r19.3rzv
    @7
    falim
    syl6bir
    adantl
    com12
    sylbi
    sylbir
    ex
    syl6bi
    com4t
    3syl
    ex
    com25
    adantl
    com15
    com12
    3ad2ant3
    syl
    impcom
    impcom
    @54
    @3
    cK
    cK
    c1
    cmin
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    @56
    @52
    @49
    @53
    @83
    cG
    cK
    cV
    frgrreggt1.v
    frrusgrord
    imp
    @56
    @83
    @6
    @52
    @56
    @82
    c3
    @3
    @56
    @82
    c2
    c2
    c1
    cmin
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    c3
    @56
    @81
    @85
    c1
    caddc
    @56
    cK
    c2
    @80
    @84
    cmul
    @56
    id
    cK
    c2
    c1
    cmin
    oveq1
    oveq12d
    oveq1d
    @86
    c2
    c1
    caddc
    co
    c3
    @85
    c2
    c1
    caddc
    @85
    c2
    c1
    cmul
    co
    c2
    @84
    c1
    c2
    cmul
    2m1e1
    oveq2i
    2t1e2
    eqtri
    oveq1i
    2p1e3
    eqtri
    syl6eq
    eqeq2d
    @51
    @6
    @7
    @16
    @6
    @7
    wi
    @46
    @29
    @6
    @7
    pm2.21
    ad2antrr
    com12
    syl6bi
    syl5com
    @49
    @53
    @55
    @56
    wo
    cG
    cK
    cV
    frgrreggt1.v
    frgrreg
    imp
    mpjaod
    exp32
    com34
    com23
    exp4c
    com34
    com25
    ex
    com23
    com14
    3imp
    com3r
    pm2.61i
    3exp
    sylbir
    ex
    syl5bir
    com25
    sylbir
    ex
    com23
    impd
    com14
    mpcom
    ex
    com14
    syl5bir
    com24
    3imp
    com25
    imp
    com14
    3imp
    sylbi
    pm2.61i
    3exp1
    mpcom
    3imp21
end
