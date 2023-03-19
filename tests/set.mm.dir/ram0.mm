include "cn0.mm"
include "wcel.mm"
include "c0.mm"
include "cram.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt2.mm"
include "eqid.mm"
include "id.mm"
include "0ex.mm"
include "a1i.mm"
include "wf.mm"
include "f0.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "f00.mm"
include "vex.mm"
include "simpl.mm"
include "hashbcval.mm"
include "sylancr.mm"
include "wne.mm"
include "wex.mm"
include "c1.mm"
include "cfz.mm"
include "cen.mm"
include "cdom.mm"
include "hashfz1.mm"
include "breq1d.mm"
include "biimpar.mm"
include "cfn.mm"
include "wb.mm"
include "fzfid.mm"
include "hashdom.mm"
include "sylancl.mm"
include "mpbid.mm"
include "domen.mm"
include "sylib.mm"
include "simprr.mm"
include "selpw.mm"
include "sylibr.mm"
include "hasheni.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "eqtr3d.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "rabn0.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "adantld.mm"
include "syl5bi.mm"
include "impr.mm"
include "ramub.mm"
include "cn.mm"
include "cc0.mm"
include "wi.mm"
include "cmin.mm"
include "clt.mm"
include "nnnn0.mm"
include "nnm1nn0.mm"
include "cbc.mm"
include "hashbc2.mm"
include "syl2anc.mm"
include "syl.mm"
include "oveq1d.mm"
include "cz.mm"
include "wo.mm"
include "nnz.mm"
include "nnre.mm"
include "ltm1d.mm"
include "olcd.mm"
include "bcval4.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "ovex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "feq2d.mm"
include "mpbiri.mm"
include "noel.mm"
include "pm2.21i.mm"
include "ramlb.mm"
include "ramubcl.mm"
include "syl32anc.mm"
include "nn0lem1lt.mm"
include "mpbird.mm"
include "nn0ge0d.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "elnn0.mm"
include "biimpi.mm"
include "mpjaod.mm"
include "nn0red.mm"
include "nn0re.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem ram0
  let cM: class M
  let vb: setvar b
  let vd: setvar d
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let cC: class C
  let va: setvar a
  let vi: setvar i
  let vy: setvar y
  let cR: class R
  let cF: class F
  let cV: class V


  assert |- ( M e. NN0 -> ( M Ramsey (/) ) = M )

  proof
    cM
    cn0
    wcel
    #
    cM
    c0
    cram
    co
    #
    cM
    wceq
    @1
    cM
    cle
    wbr
    #
    cM
    @1
    cle
    wbr
    #
    @0
    vx
    va
    vi
    cvv
    cn0
    vb
    cv
    chash
    cfv
    vi
    cv
    wceq
    vb
    va
    cv
    cpw
    crab
    cmpt2
    #
    c0
    vf
    vi
    c0
    cM
    cM
    cvv
    vs
    va
    vb
    vc
    @4
    eqid
    #
    @0
    id
    #
    c0
    cvv
    wcel
    #
    @0
    0ex
    a1i
    #
    c0
    cn0
    c0
    wf
    #
    @0
    cn0
    f0
    #
    a1i
    #
    @6
    @0
    cM
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @12
    cM
    @4
    co
    #
    c0
    vf
    cv
    #
    wf
    #
    vc
    cv
    #
    c0
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    @20
    cM
    @4
    co
    #
    @16
    ccnv
    @18
    csn
    #
    cima
    wss
    wa
    vx
    @12
    cpw
    #
    wrex
    vc
    c0
    wrex
    #
    @17
    @16
    c0
    wceq
    #
    @15
    c0
    wceq
    #
    wa
    @0
    @14
    wa
    #
    @25
    @15
    @16
    f00
    @28
    @27
    @25
    @26
    @28
    @27
    @25
    @28
    @15
    c0
    @28
    @15
    @21
    cM
    wceq
    #
    vx
    @24
    crab
    #
    c0
    @28
    @12
    cvv
    wcel
    #
    @0
    @15
    @30
    wceq
    vs
    vex
    #
    @0
    @14
    simpl
    vx
    @12
    @4
    vi
    cM
    cvv
    va
    vb
    @5
    hashbcval
    sylancr
    @28
    @29
    vx
    @24
    wrex
    #
    @30
    c0
    wne
    @28
    @20
    @24
    wcel
    #
    @29
    wa
    #
    vx
    wex
    #
    @33
    @28
    c1
    cM
    cfz
    co
    #
    @20
    cen
    wbr
    #
    @20
    @12
    wss
    #
    wa
    #
    vx
    wex
    #
    @36
    @28
    @37
    @12
    cdom
    wbr
    #
    @41
    @28
    @37
    chash
    cfv
    #
    @13
    cle
    wbr
    #
    @42
    @0
    @44
    @14
    @0
    @43
    cM
    @13
    cle
    cM
    hashfz1
    #
    breq1d
    biimpar
    @28
    @37
    cfn
    wcel
    @31
    @44
    @42
    wb
    @28
    c1
    cM
    fzfid
    @32
    @37
    @12
    cvv
    hashdom
    sylancl
    mpbid
    vx
    @37
    @12
    @32
    domen
    sylib
    @28
    @40
    @35
    vx
    @28
    @40
    @35
    @28
    @40
    wa
    #
    @34
    @29
    @46
    @39
    @34
    @28
    @38
    @39
    simprr
    vx
    @12
    selpw
    sylibr
    @46
    @43
    @21
    cM
    @38
    @43
    @21
    wceq
    @28
    @39
    @37
    @20
    hasheni
    ad2antrl
    @0
    @43
    cM
    wceq
    @14
    @40
    @45
    ad2antrr
    eqtr3d
    jca
    ex
    eximdv
    mpd
    @29
    vx
    @24
    df-rex
    sylibr
    @29
    vx
    @24
    rabn0
    sylibr
    eqnetrd
    neneqd
    pm2.21d
    adantld
    syl5bi
    impr
    ramub
    #
    @0
    cM
    cn
    wcel
    #
    @3
    cM
    cc0
    wceq
    #
    @48
    @3
    wi
    @0
    @48
    @3
    cM
    c1
    cmin
    co
    #
    @1
    clt
    wbr
    #
    @48
    vx
    @4
    c0
    vi
    c0
    c0
    cM
    @50
    cvv
    va
    vb
    vc
    @5
    cM
    nnnn0
    #
    @7
    @48
    0ex
    a1i
    @9
    @48
    @10
    a1i
    cM
    nnm1nn0
    #
    @48
    c1
    @50
    cfz
    co
    #
    cM
    @4
    co
    #
    c0
    c0
    wf
    c0
    c0
    c0
    wf
    c0
    f0
    @48
    @55
    c0
    c0
    c0
    @48
    @55
    chash
    cfv
    #
    cc0
    wceq
    #
    @55
    c0
    wceq
    #
    @48
    @56
    @54
    chash
    cfv
    #
    cM
    cbc
    co
    #
    @50
    cM
    cbc
    co
    #
    cc0
    @48
    @54
    cfn
    wcel
    @0
    @56
    @60
    wceq
    @48
    c1
    @50
    fzfid
    @52
    @54
    @4
    vi
    cM
    va
    vb
    @5
    hashbc2
    syl2anc
    @48
    @59
    @50
    cM
    cbc
    @48
    @50
    cn0
    wcel
    #
    @59
    @50
    wceq
    @53
    @50
    hashfz1
    syl
    oveq1d
    @48
    @62
    cM
    cz
    wcel
    cM
    cc0
    clt
    wbr
    #
    @50
    cM
    clt
    wbr
    #
    wo
    @61
    cc0
    wceq
    @53
    cM
    nnz
    @48
    @64
    @63
    @48
    cM
    cM
    nnre
    ltm1d
    olcd
    cM
    @50
    bcval4
    syl3anc
    3eqtrd
    @55
    cvv
    wcel
    @57
    @58
    wb
    @54
    cM
    @4
    ovex
    @55
    cvv
    hasheq0
    ax-mp
    sylib
    feq2d
    mpbiri
    @18
    c0
    wcel
    #
    @22
    c0
    ccnv
    @23
    cima
    wss
    @21
    @19
    clt
    wbr
    wi
    #
    @48
    @20
    @54
    wss
    @65
    @66
    @18
    noel
    pm2.21i
    ad2antrl
    ramlb
    @48
    @0
    @1
    cn0
    wcel
    #
    @3
    @51
    wb
    @52
    @48
    @0
    @67
    @52
    @0
    @0
    @7
    @9
    @0
    @2
    @67
    @6
    @8
    @11
    @6
    @47
    cM
    c0
    c0
    cM
    cvv
    ramubcl
    syl32anc
    #
    syl
    cM
    @1
    nn0lem1lt
    syl2anc
    mpbird
    a1i
    @0
    @3
    @49
    cc0
    @1
    cle
    wbr
    @0
    @1
    @68
    nn0ge0d
    cM
    cc0
    @1
    cle
    breq1
    syl5ibrcom
    @0
    @48
    @49
    wo
    cM
    elnn0
    biimpi
    mpjaod
    @0
    @1
    cM
    @0
    @1
    @68
    nn0red
    cM
    nn0re
    letri3d
    mpbir2and
end
