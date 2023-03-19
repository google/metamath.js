include "cpi.mm"
include "c6.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "wceq.mm"
include "ccos.mm"
include "c3.mm"
include "csqrt.mm"
include "2cn.mm"
include "cc.mm"
include "wcel.mm"
include "pire.mm"
include "6re.mm"
include "6pos.mm"
include "gt0ne0ii.mm"
include "redivcli.mm"
include "recni.mm"
include "sincl.mm"
include "ax-mp.mm"
include "2ne0.mm"
include "cmul.mm"
include "cr.mm"
include "recoscl.mm"
include "mulassi.mm"
include "sin2t.mm"
include "eqtr4i.mm"
include "caddc.mm"
include "3cn.mm"
include "3ne0.mm"
include "divcli.mm"
include "reccli.mm"
include "df-3.mm"
include "oveq1i.mm"
include "dividi.mm"
include "ax-1cn.mm"
include "divdiri.mm"
include "3eqtr3ri.mm"
include "sincosq1eq.mm"
include "mp3an.mm"
include "picn.mm"
include "divmuldivi.mm"
include "3t2e6.mm"
include "oveq2i.mm"
include "6cn.mm"
include "divassi.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "mulid2i.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "mulcli.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "pipos.mm"
include "divgt0ii.mm"
include "2lt6.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltdiv2.mm"
include "mpbi.mm"
include "w3a.mm"
include "0re.mm"
include "halfpire.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "sincosq1sgn.mm"
include "simpri.mm"
include "mulcan2.mm"
include "mvllmuli.mm"
include "cexp.mm"
include "c4.mm"
include "3re.mm"
include "3pos.mm"
include "sqrtpclii.mm"
include "sqdivi.mm"
include "cle.mm"
include "ltleii.mm"
include "sqsqrti.mm"
include "sq2.mm"
include "sqrtge0i.mm"
include "divge0i.mm"
include "sqrtsqi.mm"
include "cmin.mm"
include "4cn.mm"
include "4ne0.mm"
include "divsubdir.mm"
include "3p1e4.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "sqcli.mm"
include "sqrecii.mm"
include "sincossq.mm"
include "subaddrii.mm"

theorem sincos6thpi



  assert |- ( ( sin ` ( _pi / 6 ) ) = ( 1 / 2 ) /\ ( cos ` ( _pi / 6 ) ) = ( ( sqrt ` 3 ) / 2 ) )

  proof
    cpi
    c6
    cdiv
    co
    #
    csin
    cfv
    #
    c1
    c2
    cdiv
    co
    #
    wceq
    @0
    ccos
    cfv
    #
    c3
    csqrt
    cfv
    #
    c2
    cdiv
    co
    #
    wceq
    c2
    @1
    c1
    2cn
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    @0
    cpi
    c6
    pire
    6re
    c6
    6re
    6pos
    gt0ne0ii
    #
    redivcli
    #
    recni
    #
    @0
    sincl
    ax-mp
    #
    2ne0
    c2
    @1
    cmul
    co
    #
    @3
    cmul
    co
    #
    c1
    @3
    cmul
    co
    #
    wceq
    #
    @11
    c1
    wceq
    #
    @12
    @3
    @13
    @12
    c2
    @0
    cmul
    co
    #
    csin
    cfv
    #
    @3
    @12
    c2
    @1
    @3
    cmul
    co
    cmul
    co
    #
    @17
    c2
    @1
    @3
    2cn
    @10
    @3
    @0
    cr
    wcel
    #
    @3
    cr
    wcel
    @8
    @0
    recoscl
    ax-mp
    #
    recni
    #
    mulassi
    @6
    @17
    @18
    wceq
    @9
    @0
    sin2t
    ax-mp
    eqtr4i
    c1
    c3
    cdiv
    co
    #
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    ccos
    cfv
    #
    @17
    @3
    c2
    c3
    cdiv
    co
    #
    @23
    cmul
    co
    #
    csin
    cfv
    #
    @25
    @17
    @26
    cc
    wcel
    @22
    cc
    wcel
    @26
    @22
    caddc
    co
    #
    c1
    wceq
    @28
    @25
    wceq
    c2
    c3
    2cn
    3cn
    3ne0
    divcli
    c3
    3cn
    3ne0
    reccli
    c3
    c3
    cdiv
    co
    c2
    c1
    caddc
    co
    #
    c3
    cdiv
    co
    c1
    @29
    c3
    @30
    c3
    cdiv
    df-3
    oveq1i
    c3
    3cn
    3ne0
    dividi
    c2
    c1
    c3
    2cn
    ax-1cn
    3cn
    3ne0
    divdiri
    3eqtr3ri
    @26
    @22
    sincosq1eq
    mp3an
    @27
    @16
    csin
    @27
    c2
    cpi
    cmul
    co
    #
    c3
    c2
    cmul
    co
    #
    cdiv
    co
    @31
    c6
    cdiv
    co
    @16
    c2
    c3
    cpi
    c2
    2cn
    3cn
    picn
    2cn
    3ne0
    2ne0
    divmuldivi
    @32
    c6
    @31
    cdiv
    3t2e6
    oveq2i
    c2
    cpi
    c6
    2cn
    picn
    6cn
    @7
    divassi
    3eqtri
    fveq2i
    eqtr3i
    @24
    @0
    ccos
    @24
    c1
    cpi
    cmul
    co
    #
    @32
    cdiv
    co
    @0
    c1
    c3
    cpi
    c2
    ax-1cn
    3cn
    picn
    2cn
    3ne0
    2ne0
    divmuldivi
    @33
    cpi
    @32
    c6
    cdiv
    cpi
    picn
    mulid2i
    3t2e6
    oveq12i
    eqtri
    fveq2i
    eqtr3i
    eqtri
    @3
    @21
    mulid2i
    eqtr4i
    @11
    cc
    wcel
    c1
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    wa
    @14
    @15
    wb
    c2
    @1
    2cn
    @10
    mulcli
    ax-1cn
    @35
    @36
    @21
    @3
    @20
    cc0
    @1
    clt
    wbr
    #
    cc0
    @3
    clt
    wbr
    #
    @0
    cc0
    @23
    cioo
    co
    wcel
    #
    @37
    @38
    wa
    @39
    @19
    cc0
    @0
    clt
    wbr
    #
    @0
    @23
    clt
    wbr
    #
    @8
    cpi
    c6
    pire
    6re
    pipos
    6pos
    divgt0ii
    c2
    c6
    clt
    wbr
    #
    @41
    2lt6
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    c6
    cr
    wcel
    #
    cc0
    c6
    clt
    wbr
    #
    wa
    cpi
    cr
    wcel
    #
    cc0
    cpi
    clt
    wbr
    #
    wa
    @42
    @41
    wb
    @43
    @44
    2re
    2pos
    pm3.2i
    @45
    @46
    6re
    6pos
    pm3.2i
    @47
    @48
    pire
    pipos
    pm3.2i
    c2
    c6
    cpi
    ltdiv2
    mp3an
    mpbi
    cc0
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @39
    @19
    @40
    @41
    w3a
    wb
    #
    0re
    halfpire
    @49
    cc0
    cxr
    wcel
    @23
    cxr
    wcel
    @51
    @50
    cc0
    rexr
    @23
    rexr
    cc0
    @23
    @0
    elioo2
    syl2an
    mp2an
    mpbir3an
    @0
    sincosq1sgn
    ax-mp
    simpri
    #
    gt0ne0ii
    pm3.2i
    @11
    c1
    @3
    mulcan2
    mp3an
    mpbi
    mvllmuli
    #
    @5
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c3
    c4
    cdiv
    co
    #
    csqrt
    cfv
    #
    @5
    @3
    @54
    @56
    csqrt
    @54
    @4
    c2
    cexp
    co
    #
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    @56
    @4
    c2
    @4
    c3
    3re
    3pos
    sqrtpclii
    #
    recni
    2cn
    2ne0
    sqdivi
    @58
    c3
    @59
    c4
    cdiv
    cc0
    c3
    cle
    wbr
    #
    @58
    c3
    wceq
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    #
    c3
    3re
    sqsqrti
    ax-mp
    sq2
    oveq12i
    eqtri
    fveq2i
    cc0
    @5
    cle
    wbr
    #
    @55
    @5
    wceq
    cc0
    @4
    cle
    wbr
    #
    @44
    @63
    @61
    @64
    @62
    c3
    3re
    sqrtge0i
    ax-mp
    2pos
    @4
    c2
    @60
    2re
    divge0i
    mp2an
    @5
    @4
    c2
    @60
    2re
    2ne0
    redivcli
    sqrtsqi
    ax-mp
    @3
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @57
    @3
    @65
    @56
    csqrt
    c4
    c4
    cdiv
    co
    #
    c1
    c4
    cdiv
    co
    #
    cmin
    co
    #
    c1
    @68
    cmin
    co
    @56
    @65
    @67
    c1
    @68
    cmin
    c4
    4cn
    4ne0
    dividi
    oveq1i
    c4
    c1
    cmin
    co
    #
    c4
    cdiv
    co
    #
    @69
    @56
    c4
    cc
    wcel
    #
    @34
    @72
    c4
    cc0
    wne
    #
    wa
    @71
    @69
    wceq
    4cn
    ax-1cn
    @72
    @73
    4cn
    4ne0
    pm3.2i
    c4
    c1
    c4
    divsubdir
    mp3an
    @70
    c3
    c4
    cdiv
    @70
    c3
    wceq
    c3
    c1
    caddc
    co
    c4
    wceq
    3p1e4
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    subadd2i
    mpbir
    oveq1i
    eqtr3i
    c1
    @68
    @65
    ax-1cn
    c4
    4cn
    4ne0
    reccli
    @3
    @21
    sqcli
    @1
    c2
    cexp
    co
    #
    @65
    caddc
    co
    #
    @68
    @65
    caddc
    co
    c1
    @74
    @68
    @65
    caddc
    @74
    @2
    c2
    cexp
    co
    c1
    @59
    cdiv
    co
    @68
    @1
    @2
    c2
    cexp
    @53
    oveq1i
    c2
    2cn
    2ne0
    sqrecii
    @59
    c4
    c1
    cdiv
    sq2
    oveq2i
    3eqtri
    oveq1i
    @6
    @75
    c1
    wceq
    @9
    @0
    sincossq
    ax-mp
    eqtr3i
    subaddrii
    3eqtr3ri
    fveq2i
    cc0
    @3
    cle
    wbr
    @66
    @3
    wceq
    cc0
    @3
    0re
    @20
    @52
    ltleii
    @3
    @20
    sqrtsqi
    ax-mp
    eqtr3i
    3eqtr3ri
    pm3.2i
end
