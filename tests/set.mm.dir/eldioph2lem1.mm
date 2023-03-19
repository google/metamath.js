include "cn0.mm"
include "wcel.mm"
include "cfn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "caddc.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "cv.mm"
include "wf1o.mm"
include "cres.mm"
include "cid.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wrex.mm"
include "cuz.mm"
include "cen.mm"
include "wbr.mm"
include "wex.mm"
include "cc.mm"
include "cr.mm"
include "nn0re.mm"
include "3ad2ant1.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "diffi.mm"
include "3ad2ant2.mm"
include "fzfid.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "hashun.mm"
include "syl3anc.mm"
include "uncom.mm"
include "simp3.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "hashfz1.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "cz.mm"
include "1zzd.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "nn0z.mm"
include "fzen.mm"
include "ensymd.mm"
include "wb.mm"
include "fzfi.mm"
include "hashen.mm"
include "mp2an.mm"
include "sylibr.mm"
include "3eqtrd.mm"
include "sylancr.mm"
include "mpbid.mm"
include "bren.mm"
include "cle.mm"
include "simpl1.mm"
include "simpl2.mm"
include "nn0addge2.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "adantr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "vex.mm"
include "ovex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "unex.mm"
include "simpr.mm"
include "f1oi.mm"
include "clt.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "fzsplit1nn0.mm"
include "syl6reqr.mm"
include "simpl3.mm"
include "f1oeq23.mm"
include "resundir.mm"
include "cdm.mm"
include "dmres.mm"
include "f1odm.mm"
include "adantl.mm"
include "ineq2d.mm"
include "eqtrd.mm"
include "wrel.mm"
include "relres.mm"
include "reldm0.mm"
include "residm.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "f1oeq2.mm"
include "anbi1d.mm"
include "f1oeq1.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "exlimddv.mm"

theorem eldioph2lem1
  let cA: class A
  let ve: setvar e
  let cN: class N
  let vd: setvar d
  let va: setvar a

  disjoint A d
  disjoint A e
  disjoint d e
  disjoint N d
  disjoint N e
  disjoint A a
  disjoint a d
  disjoint a e
  disjoint N a
  assert |- ( ( N e. NN0 /\ A e. Fin /\ ( 1 ... N ) C_ A ) -> E. d e. ( ZZ>= ` N ) E. e e. _V ( e : ( 1 ... d ) -1-1-onto-> A /\ ( e |` ( 1 ... N ) ) = ( _I |` ( 1 ... N ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cfn
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cA
    wss
    #
    w3a
    #
    cN
    c1
    caddc
    co
    #
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    @2
    cdif
    #
    va
    cv
    #
    wf1o
    #
    c1
    vd
    cv
    #
    cfz
    co
    #
    cA
    ve
    cv
    #
    wf1o
    #
    @13
    @2
    cres
    #
    cid
    @2
    cres
    #
    wceq
    #
    wa
    #
    ve
    cvv
    wrex
    vd
    cN
    cuz
    cfv
    #
    wrex
    #
    va
    @4
    @7
    @8
    cen
    wbr
    #
    @10
    va
    wex
    @4
    @7
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    wceq
    #
    @21
    @4
    @22
    c1
    cN
    caddc
    co
    #
    @23
    cN
    caddc
    co
    #
    cfz
    co
    #
    chash
    cfv
    #
    c1
    @23
    cfz
    co
    #
    chash
    cfv
    #
    @23
    @4
    @7
    @27
    chash
    @4
    @5
    @25
    @6
    @26
    cfz
    @4
    cN
    cc
    wcel
    c1
    cc
    wcel
    @5
    @25
    wceq
    @4
    cN
    @0
    @1
    cN
    cr
    wcel
    #
    @3
    cN
    nn0re
    3ad2ant1
    #
    recnd
    ax-1cn
    cN
    c1
    addcom
    sylancl
    @4
    @8
    @2
    cun
    #
    chash
    cfv
    #
    @23
    @2
    chash
    cfv
    #
    caddc
    co
    #
    @6
    @26
    @4
    @8
    cfn
    wcel
    #
    @2
    cfn
    wcel
    @8
    @2
    cin
    #
    c0
    wceq
    #
    @34
    @36
    wceq
    @1
    @0
    @37
    @3
    cA
    @2
    diffi
    3ad2ant2
    #
    @4
    c1
    cN
    fzfid
    @39
    @4
    @38
    @2
    @8
    cin
    c0
    @8
    @2
    incom
    @2
    cA
    disjdif
    eqtri
    #
    a1i
    @8
    @2
    hashun
    syl3anc
    @4
    @33
    cA
    chash
    @4
    @33
    @2
    @8
    cun
    #
    cA
    @8
    @2
    uncom
    #
    @4
    @3
    @42
    cA
    wceq
    #
    @0
    @1
    @3
    simp3
    @2
    cA
    undif
    #
    sylib
    syl5eq
    fveq2d
    @4
    @35
    cN
    @23
    caddc
    @0
    @1
    @35
    cN
    wceq
    @3
    cN
    hashfz1
    3ad2ant1
    oveq2d
    3eqtr3d
    #
    oveq12d
    fveq2d
    @4
    @27
    @29
    cen
    wbr
    #
    @28
    @30
    wceq
    #
    @4
    @29
    @27
    @4
    c1
    cz
    wcel
    @23
    cz
    wcel
    cN
    cz
    wcel
    #
    @29
    @27
    cen
    wbr
    @4
    1zzd
    @4
    @23
    @4
    @37
    @23
    cn0
    wcel
    #
    @40
    @8
    hashcl
    syl
    #
    nn0zd
    @0
    @1
    @49
    @3
    cN
    nn0z
    3ad2ant1
    cN
    c1
    @23
    fzen
    syl3anc
    ensymd
    @27
    cfn
    wcel
    @29
    cfn
    wcel
    @48
    @47
    wb
    @25
    @26
    fzfi
    c1
    @23
    fzfi
    @27
    @29
    hashen
    mp2an
    sylibr
    @4
    @50
    @30
    @23
    wceq
    @51
    @23
    hashfz1
    syl
    3eqtrd
    @4
    @7
    cfn
    wcel
    @37
    @24
    @21
    wb
    @5
    @6
    fzfi
    @40
    @7
    @8
    hashen
    sylancr
    mpbid
    @7
    @8
    va
    bren
    sylib
    @4
    @10
    wa
    #
    @6
    @19
    wcel
    #
    @9
    @16
    cun
    #
    cvv
    wcel
    #
    c1
    @6
    cfz
    co
    #
    cA
    @54
    wf1o
    #
    @54
    @2
    cres
    #
    @16
    wceq
    #
    @20
    @52
    @49
    @6
    cz
    wcel
    cN
    @6
    cle
    wbr
    #
    @53
    @52
    cN
    @0
    @1
    @3
    @10
    simpl1
    #
    nn0zd
    @52
    @6
    @52
    @1
    @6
    cn0
    wcel
    #
    @0
    @1
    @3
    @10
    simpl2
    cA
    hashcl
    syl
    #
    nn0zd
    @4
    @60
    @10
    @4
    cN
    @26
    @6
    cle
    @4
    @31
    @50
    cN
    @26
    cle
    wbr
    @32
    @51
    cN
    @23
    nn0addge2
    syl2anc
    @46
    breqtrrd
    adantr
    #
    cN
    @6
    eluz2
    syl3anbrc
    @55
    @52
    @9
    @16
    va
    vex
    @2
    cvv
    wcel
    @16
    cvv
    wcel
    c1
    cN
    cfz
    ovex
    @2
    cvv
    resiexg
    ax-mp
    unex
    a1i
    @52
    @7
    @2
    cun
    #
    @33
    @54
    wf1o
    #
    @57
    @52
    @10
    @2
    @2
    @16
    wf1o
    #
    @7
    @2
    cin
    #
    c0
    wceq
    @39
    @66
    @4
    @10
    simpr
    @67
    @52
    @2
    f1oi
    a1i
    @52
    @68
    @2
    @7
    cin
    #
    c0
    @7
    @2
    incom
    @52
    cN
    @5
    clt
    wbr
    @69
    c0
    wceq
    @52
    cN
    @52
    cN
    @61
    nn0red
    ltp1d
    c1
    cN
    @5
    @6
    fzdisj
    syl
    #
    syl5eq
    @39
    @52
    @41
    a1i
    @7
    @8
    @2
    @2
    @9
    @16
    f1oun
    syl22anc
    @52
    @65
    @56
    wceq
    @33
    cA
    wceq
    @66
    @57
    wb
    @52
    @56
    @2
    @7
    cun
    #
    @65
    @52
    @0
    @62
    @60
    @56
    @71
    wceq
    @61
    @63
    @64
    cN
    @6
    fzsplit1nn0
    syl3anc
    @7
    @2
    uncom
    syl6reqr
    @52
    @33
    @42
    cA
    @43
    @52
    @3
    @44
    @0
    @1
    @3
    @10
    simpl3
    @45
    sylib
    syl5eq
    @65
    @56
    @33
    cA
    @54
    f1oeq23
    syl2anc
    mpbid
    @52
    @58
    @9
    @2
    cres
    #
    @16
    @2
    cres
    #
    cun
    #
    @16
    @9
    @16
    @2
    resundir
    @52
    @74
    c0
    @16
    cun
    #
    @16
    @52
    @72
    c0
    @73
    @16
    @52
    @72
    cdm
    #
    c0
    wceq
    #
    @72
    c0
    wceq
    #
    @52
    @76
    @2
    @9
    cdm
    #
    cin
    #
    c0
    @9
    @2
    dmres
    @52
    @80
    @69
    c0
    @52
    @79
    @7
    @2
    @10
    @79
    @7
    wceq
    @4
    @7
    @8
    @9
    f1odm
    adantl
    ineq2d
    @70
    eqtrd
    syl5eq
    @72
    wrel
    @78
    @77
    wb
    @9
    @2
    relres
    @72
    reldm0
    ax-mp
    sylibr
    @73
    @16
    wceq
    @52
    cid
    @2
    residm
    a1i
    uneq12d
    @75
    @16
    c0
    cun
    @16
    c0
    @16
    uncom
    @16
    un0
    eqtri
    syl6eq
    syl5eq
    @18
    @57
    @59
    wa
    @56
    cA
    @13
    wf1o
    #
    @17
    wa
    vd
    ve
    @6
    @54
    @19
    cvv
    @11
    @6
    wceq
    #
    @14
    @81
    @17
    @82
    @12
    @56
    wceq
    @14
    @81
    wb
    @11
    @6
    c1
    cfz
    oveq2
    @12
    @56
    cA
    @13
    f1oeq2
    syl
    anbi1d
    @13
    @54
    wceq
    #
    @81
    @57
    @17
    @59
    @56
    cA
    @13
    @54
    f1oeq1
    @83
    @15
    @58
    @16
    @13
    @54
    @2
    reseq1
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    exlimddv
end
