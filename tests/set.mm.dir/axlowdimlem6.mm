include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cop.mm"
include "cpr.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "wne.mm"
include "wrex.mm"
include "wn.mm"
include "cz.mm"
include "cle.mm"
include "wa.mm"
include "1zzd.mm"
include "eluzelz.mm"
include "cn.mm"
include "wss.mm"
include "2nn.mm"
include "uznnssnn.mm"
include "ax-mp.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "sseli.mm"
include "eluzle.mm"
include "syl.mm"
include "1re.mm"
include "leidi.mm"
include "jctil.mm"
include "elfz4.mm"
include "syl31anc.mm"
include "eluzel2.mm"
include "1le2.mm"
include "ax-1ne0.mm"
include "1t1e1.mm"
include "0cn.mm"
include "mul01i.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "fveq2.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "cr.mm"
include "wf.mm"
include "0re.mm"
include "axlowdimlem4.mm"
include "ffn.mm"
include "axlowdimlem1.mm"
include "axlowdimlem2.mm"
include "w3a.mm"
include "1z.mm"
include "2z.mm"
include "3pm3.2i.mm"
include "pm3.2i.mm"
include "mp2an.mm"
include "fvun1.mm"
include "mp3an.mm"
include "1ne2.mm"
include "1ex.mm"
include "fvpr1.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "elexi.mm"
include "oveq12d.mm"
include "1m0e1.mm"
include "oveq1d.mm"
include "0m0e0.mm"
include "oveq2d.mm"
include "neeq12d.mm"
include "2re.mm"
include "fvpr2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"
include "cee.mm"
include "wb.mm"
include "axlowdimlem5.mm"
include "colinearalg.mm"
include "syl3anc.mm"
include "mtbird.mm"
include "opeq12i.mm"
include "breq12i.mm"
include "3orbi123i.mm"
include "sylnibr.mm"

theorem axlowdimlem6
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume axlowdimlem6.1: |- A = ( { <. 1 , 0 >. , <. 2 , 0 >. } u. ( ( 3 ... N ) X. { 0 } ) )
  assume axlowdimlem6.2: |- B = ( { <. 1 , 1 >. , <. 2 , 0 >. } u. ( ( 3 ... N ) X. { 0 } ) )
  assume axlowdimlem6.3: |- C = ( { <. 1 , 0 >. , <. 2 , 1 >. } u. ( ( 3 ... N ) X. { 0 } ) )


  assert |- ( N e. ( ZZ>= ` 2 ) -> -. ( A Btwn <. B , C >. \/ B Btwn <. C , A >. \/ C Btwn <. A , B >. ) )

  proof
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    c1
    cc0
    cop
    #
    c2
    cc0
    cop
    #
    cpr
    #
    c3
    cN
    cfz
    co
    #
    cc0
    csn
    cxp
    #
    cun
    #
    c1
    c1
    cop
    @3
    cpr
    #
    @6
    cun
    #
    @2
    c2
    c1
    cop
    cpr
    #
    @6
    cun
    #
    cop
    #
    cbtwn
    wbr
    #
    @9
    @11
    @7
    cop
    #
    cbtwn
    wbr
    #
    @11
    @7
    @9
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    cA
    cB
    cC
    cop
    #
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    #
    cbtwn
    wbr
    #
    cC
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    w3o
    @1
    @18
    vi
    cv
    #
    @9
    cfv
    #
    @25
    @7
    cfv
    #
    cmin
    co
    #
    vj
    cv
    #
    @11
    cfv
    #
    @29
    @7
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @29
    @9
    cfv
    #
    @31
    cmin
    co
    #
    @25
    @11
    cfv
    #
    @27
    cmin
    co
    #
    cmul
    co
    #
    wceq
    #
    vj
    c1
    cN
    cfz
    co
    #
    wral
    #
    vi
    @40
    wral
    #
    @1
    @33
    @38
    wne
    #
    vj
    @40
    wrex
    #
    vi
    @40
    wrex
    #
    @42
    wn
    #
    @1
    c1
    @40
    wcel
    #
    c2
    @40
    wcel
    #
    @45
    @1
    c1
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @49
    c1
    c1
    cle
    wbr
    #
    c1
    cN
    cle
    wbr
    #
    wa
    @47
    @1
    1zzd
    #
    c2
    cN
    eluzelz
    #
    @53
    @1
    @52
    @51
    @1
    cN
    c1
    cuz
    cfv
    #
    wcel
    @52
    @0
    @55
    cN
    @0
    cn
    @55
    c2
    cn
    wcel
    @0
    cn
    wss
    2nn
    c2
    uznnssnn
    ax-mp
    nnuz
    sseqtri
    sseli
    c1
    cN
    eluzle
    syl
    c1
    1re
    leidi
    #
    jctil
    c1
    c1
    cN
    elfz4
    syl31anc
    @1
    @49
    @50
    c2
    cz
    wcel
    #
    c1
    c2
    cle
    wbr
    #
    c2
    cN
    cle
    wbr
    #
    wa
    @48
    @53
    @54
    c2
    cN
    eluzel2
    @1
    @59
    @58
    c2
    cN
    eluzle
    1le2
    jctil
    c2
    c1
    cN
    elfz4
    syl31anc
    @47
    @48
    c1
    c1
    cmul
    co
    #
    cc0
    cc0
    cmul
    co
    #
    wne
    #
    @45
    @62
    c1
    cc0
    wne
    ax-1ne0
    @60
    c1
    @61
    cc0
    1t1e1
    cc0
    0cn
    mul01i
    neeq12i
    mpbir
    @43
    @62
    c1
    @32
    cmul
    co
    #
    @35
    cc0
    cmul
    co
    #
    wne
    vi
    vj
    c1
    c2
    @40
    @40
    @25
    c1
    wceq
    #
    @33
    @63
    @38
    @64
    @65
    @28
    c1
    @32
    cmul
    @65
    @28
    c1
    cc0
    cmin
    co
    #
    c1
    @65
    @26
    c1
    @27
    cc0
    cmin
    @65
    @26
    c1
    @9
    cfv
    #
    c1
    @25
    c1
    @9
    fveq2
    @67
    c1
    @8
    cfv
    #
    c1
    @8
    c1
    c2
    cfz
    co
    #
    wfn
    #
    @6
    @5
    wfn
    #
    @69
    @5
    cin
    c0
    wceq
    #
    c1
    @69
    wcel
    #
    wa
    #
    @67
    @68
    wceq
    @69
    cr
    @8
    wf
    @70
    c1
    cc0
    1re
    0re
    axlowdimlem4
    @69
    cr
    @8
    ffn
    ax-mp
    #
    @5
    cr
    @6
    wf
    @71
    cN
    axlowdimlem1
    @5
    cr
    @6
    ffn
    ax-mp
    #
    @72
    @73
    cN
    axlowdimlem2
    #
    @49
    @57
    @49
    w3a
    @51
    @58
    wa
    @73
    @49
    @57
    @49
    1z
    2z
    1z
    3pm3.2i
    @51
    @58
    @56
    1le2
    pm3.2i
    c1
    c1
    c2
    elfz4
    mp2an
    pm3.2i
    #
    @69
    @5
    @8
    @6
    c1
    fvun1
    mp3an
    c1
    c2
    wne
    #
    @68
    c1
    wceq
    1ne2
    c1
    c2
    c1
    cc0
    1ex
    1ex
    fvpr1
    ax-mp
    eqtri
    syl6eq
    @65
    @27
    c1
    @7
    cfv
    #
    cc0
    @25
    c1
    @7
    fveq2
    @80
    c1
    @4
    cfv
    #
    cc0
    @4
    @69
    wfn
    #
    @71
    @74
    @80
    @81
    wceq
    @69
    cr
    @4
    wf
    @82
    cc0
    cc0
    0re
    0re
    axlowdimlem4
    @69
    cr
    @4
    ffn
    ax-mp
    #
    @76
    @78
    @69
    @5
    @4
    @6
    c1
    fvun1
    mp3an
    @79
    @81
    cc0
    wceq
    1ne2
    c1
    c2
    cc0
    cc0
    1ex
    cc0
    cr
    0re
    elexi
    #
    fvpr1
    ax-mp
    eqtri
    syl6eq
    #
    oveq12d
    1m0e1
    syl6eq
    oveq1d
    @65
    @37
    cc0
    @35
    cmul
    @65
    @37
    cc0
    cc0
    cmin
    co
    #
    cc0
    @65
    @36
    cc0
    @27
    cc0
    cmin
    @65
    @36
    c1
    @11
    cfv
    #
    cc0
    @25
    c1
    @11
    fveq2
    @87
    c1
    @10
    cfv
    #
    cc0
    @10
    @69
    wfn
    #
    @71
    @74
    @87
    @88
    wceq
    @69
    cr
    @10
    wf
    @89
    cc0
    c1
    0re
    1re
    axlowdimlem4
    @69
    cr
    @10
    ffn
    ax-mp
    #
    @76
    @78
    @69
    @5
    @10
    @6
    c1
    fvun1
    mp3an
    @79
    @88
    cc0
    wceq
    1ne2
    c1
    c2
    cc0
    c1
    1ex
    @84
    fvpr1
    ax-mp
    eqtri
    syl6eq
    @85
    oveq12d
    0m0e0
    syl6eq
    oveq2d
    neeq12d
    @29
    c2
    wceq
    #
    @63
    @60
    @64
    @61
    @91
    @32
    c1
    c1
    cmul
    @91
    @32
    @66
    c1
    @91
    @30
    c1
    @31
    cc0
    cmin
    @91
    @30
    c2
    @11
    cfv
    #
    c1
    @29
    c2
    @11
    fveq2
    @92
    c2
    @10
    cfv
    #
    c1
    @89
    @71
    @72
    c2
    @69
    wcel
    #
    wa
    #
    @92
    @93
    wceq
    @90
    @76
    @72
    @94
    @77
    @49
    @57
    @57
    w3a
    @58
    c2
    c2
    cle
    wbr
    #
    wa
    @94
    @49
    @57
    @57
    1z
    2z
    2z
    3pm3.2i
    @58
    @96
    1le2
    c2
    2re
    leidi
    pm3.2i
    c2
    c1
    c2
    elfz4
    mp2an
    pm3.2i
    #
    @69
    @5
    @10
    @6
    c2
    fvun1
    mp3an
    @79
    @93
    c1
    wceq
    1ne2
    c1
    c2
    cc0
    c1
    c2
    cz
    2z
    elexi
    #
    1ex
    fvpr2
    ax-mp
    eqtri
    syl6eq
    @91
    @31
    c2
    @7
    cfv
    #
    cc0
    @29
    c2
    @7
    fveq2
    @99
    c2
    @4
    cfv
    #
    cc0
    @82
    @71
    @95
    @99
    @100
    wceq
    @83
    @76
    @97
    @69
    @5
    @4
    @6
    c2
    fvun1
    mp3an
    @79
    @100
    cc0
    wceq
    1ne2
    c1
    c2
    cc0
    cc0
    @98
    @84
    fvpr2
    ax-mp
    eqtri
    syl6eq
    #
    oveq12d
    1m0e1
    syl6eq
    oveq2d
    @91
    @35
    cc0
    cc0
    cmul
    @91
    @35
    @86
    cc0
    @91
    @34
    cc0
    @31
    cc0
    cmin
    @91
    @34
    c2
    @9
    cfv
    #
    cc0
    @29
    c2
    @9
    fveq2
    @102
    c2
    @8
    cfv
    #
    cc0
    @70
    @71
    @95
    @102
    @103
    wceq
    @75
    @76
    @97
    @69
    @5
    @8
    @6
    c2
    fvun1
    mp3an
    @79
    @103
    cc0
    wceq
    1ne2
    c1
    c2
    c1
    cc0
    @98
    @84
    fvpr2
    ax-mp
    eqtri
    syl6eq
    @101
    oveq12d
    0m0e0
    syl6eq
    oveq1d
    neeq12d
    rspc2ev
    mp3an3
    syl2anc
    @45
    @41
    wn
    #
    vi
    @40
    wrex
    @46
    @44
    @104
    vi
    @40
    @44
    @39
    wn
    #
    vj
    @40
    wrex
    @104
    @43
    @105
    vj
    @40
    @33
    @38
    df-ne
    rexbii
    @39
    vj
    @40
    rexnal
    bitri
    rexbii
    @41
    vi
    @40
    rexnal
    bitri
    sylib
    @1
    @7
    cN
    cee
    cfv
    #
    wcel
    @9
    @106
    wcel
    @11
    @106
    wcel
    @18
    @42
    wb
    cc0
    cc0
    cN
    0re
    0re
    axlowdimlem5
    c1
    cc0
    cN
    1re
    0re
    axlowdimlem5
    cc0
    c1
    cN
    0re
    1re
    axlowdimlem5
    @7
    @9
    @11
    vi
    vj
    cN
    colinearalg
    syl3anc
    mtbird
    @20
    @13
    @22
    @15
    @24
    @17
    cA
    @7
    @19
    @12
    cbtwn
    axlowdimlem6.1
    cB
    @9
    cC
    @11
    axlowdimlem6.2
    axlowdimlem6.3
    opeq12i
    breq12i
    cB
    @9
    @21
    @14
    cbtwn
    axlowdimlem6.2
    cC
    @11
    cA
    @7
    axlowdimlem6.3
    axlowdimlem6.1
    opeq12i
    breq12i
    cC
    @11
    @23
    @16
    cbtwn
    axlowdimlem6.3
    cA
    @7
    cB
    @9
    axlowdimlem6.1
    axlowdimlem6.2
    opeq12i
    breq12i
    3orbi123i
    sylnibr
end
