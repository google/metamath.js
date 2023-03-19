include "c7.mm"
include "c9.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "c2.mm"
include "ccos.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "7cn.mm"
include "9cn.mm"
include "9re.mm"
include "9pos.mm"
include "gt0ne0ii.mm"
include "divneg.mm"
include "mp3an.mm"
include "wa.mm"
include "2cn.mm"
include "pm3.2i.mm"
include "divsubdir.mm"
include "negsubdi2i.mm"
include "caddc.mm"
include "7p2e9.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "dividi.mm"
include "oveq2i.mm"
include "3eqtr2ri.mm"
include "ax-1cn.mm"
include "divassi.mm"
include "2t1e2.mm"
include "c3.mm"
include "3cn.mm"
include "3ne0.mm"
include "sqdivi.mm"
include "sq1.mm"
include "sq3.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "cos1bnd.mm"
include "simpli.mm"
include "cle.mm"
include "wb.mm"
include "0le1.mm"
include "3pos.mm"
include "1re.mm"
include "3re.mm"
include "divge0i.mm"
include "mp2an.mm"
include "0re.mm"
include "cr.mm"
include "recoscl.mm"
include "ax-mp.mm"
include "rereccli.mm"
include "lelttri.mm"
include "ltleii.mm"
include "lt2sqi.mm"
include "mpbi.mm"
include "eqbrtrri.mm"
include "2pos.mm"
include "resqcli.mm"
include "2re.mm"
include "ltmul2i.mm"
include "redivcli.mm"
include "remulcli.mm"
include "ltsub1.mm"
include "fveq2i.mm"
include "cos2t.mm"
include "breqtrri.mm"
include "c8.mm"
include "c4.mm"
include "simpri.mm"
include "0le2.mm"
include "sq2.mm"
include "breqtri.mm"
include "4re.mm"
include "4cn.mm"
include "4t2e8.mm"
include "mulcomli.mm"
include "8re.mm"
include "8cn.mm"
include "8p1e9.mm"
include "subaddrii.mm"
include "eqbrtri.mm"

theorem cos2bnd



  assert |- ( -u ( 7 / 9 ) < ( cos ` 2 ) /\ ( cos ` 2 ) < -u ( 1 / 9 ) )

  proof
    c7
    c9
    cdiv
    co
    cneg
    #
    c2
    ccos
    cfv
    #
    clt
    wbr
    @1
    c1
    c9
    cdiv
    co
    #
    cneg
    #
    clt
    wbr
    @0
    c2
    c1
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cmin
    co
    #
    @1
    clt
    c2
    c9
    cdiv
    co
    #
    c1
    cmin
    co
    #
    @0
    @7
    clt
    @0
    c7
    cneg
    #
    c9
    cdiv
    co
    #
    @8
    c9
    c9
    cdiv
    co
    #
    cmin
    co
    #
    @9
    c7
    cc
    wcel
    c9
    cc
    wcel
    #
    c9
    cc0
    wne
    #
    @0
    @11
    wceq
    7cn
    9cn
    c9
    9re
    9pos
    gt0ne0ii
    #
    c7
    c9
    divneg
    mp3an
    c2
    c9
    cmin
    co
    #
    c9
    cdiv
    co
    #
    @13
    @11
    c2
    cc
    wcel
    @14
    @14
    @15
    wa
    #
    @18
    @13
    wceq
    2cn
    9cn
    @14
    @15
    9cn
    @16
    pm3.2i
    #
    c2
    c9
    c9
    divsubdir
    mp3an
    @17
    @10
    c9
    cdiv
    c9
    c2
    cmin
    co
    #
    cneg
    @17
    @10
    c9
    c2
    9cn
    2cn
    negsubdi2i
    @21
    c7
    @21
    c7
    wceq
    c7
    c2
    caddc
    co
    c9
    wceq
    7p2e9
    c9
    c2
    c7
    9cn
    2cn
    7cn
    subadd2i
    mpbir
    negeqi
    eqtr3i
    oveq1i
    eqtr3i
    @12
    c1
    @8
    cmin
    c9
    9cn
    @16
    dividi
    #
    oveq2i
    3eqtr2ri
    @8
    @6
    clt
    wbr
    #
    @9
    @7
    clt
    wbr
    #
    c2
    @2
    cmul
    co
    #
    @8
    @6
    clt
    c2
    c1
    cmul
    co
    #
    c9
    cdiv
    co
    @25
    @8
    c2
    c1
    c9
    2cn
    ax-1cn
    9cn
    @16
    divassi
    @26
    c2
    c9
    cdiv
    2t1e2
    oveq1i
    eqtr3i
    @2
    @5
    clt
    wbr
    #
    @25
    @6
    clt
    wbr
    #
    c1
    c3
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @2
    @5
    clt
    @30
    c1
    c2
    cexp
    co
    #
    c3
    c2
    cexp
    co
    #
    cdiv
    co
    @2
    c1
    c3
    ax-1cn
    3cn
    3ne0
    sqdivi
    @31
    c1
    @32
    c9
    cdiv
    sq1
    sq3
    oveq12i
    eqtri
    @29
    @4
    clt
    wbr
    #
    @30
    @5
    clt
    wbr
    #
    @33
    @4
    c2
    c3
    cdiv
    co
    #
    clt
    wbr
    #
    cos1bnd
    simpli
    #
    cc0
    @29
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @33
    @34
    wb
    cc0
    c1
    cle
    wbr
    cc0
    c3
    clt
    wbr
    #
    @38
    0le1
    3pos
    c1
    c3
    1re
    3re
    divge0i
    mp2an
    #
    cc0
    @4
    0re
    c1
    cr
    wcel
    #
    @4
    cr
    wcel
    1re
    c1
    recoscl
    ax-mp
    #
    @38
    @33
    cc0
    @4
    clt
    wbr
    @41
    @37
    cc0
    @29
    @4
    0re
    c3
    3re
    3ne0
    rereccli
    #
    @43
    lelttri
    mp2an
    ltleii
    #
    @29
    @4
    @44
    @43
    lt2sqi
    mp2an
    mpbi
    eqbrtrri
    cc0
    c2
    clt
    wbr
    #
    @27
    @28
    wb
    2pos
    @2
    @5
    c2
    c9
    9re
    @16
    rereccli
    @4
    @43
    resqcli
    #
    2re
    ltmul2i
    ax-mp
    mpbi
    eqbrtrri
    @8
    cr
    wcel
    @6
    cr
    wcel
    #
    @42
    @23
    @24
    wb
    c2
    c9
    2re
    9re
    @16
    redivcli
    c2
    @5
    2re
    @47
    remulcli
    #
    1re
    @8
    @6
    c1
    ltsub1
    mp3an
    mpbi
    eqbrtrri
    @26
    ccos
    cfv
    #
    @1
    @7
    @26
    c2
    ccos
    2t1e2
    fveq2i
    c1
    cc
    wcel
    #
    @50
    @7
    wceq
    ax-1cn
    c1
    cos2t
    ax-mp
    eqtr3i
    #
    breqtrri
    @1
    @7
    @3
    clt
    @52
    @7
    c8
    c9
    cdiv
    co
    #
    c1
    cmin
    co
    #
    @3
    clt
    @6
    @53
    clt
    wbr
    #
    @7
    @54
    clt
    wbr
    #
    @6
    c2
    c4
    c9
    cdiv
    co
    #
    cmul
    co
    #
    @53
    clt
    @5
    @57
    clt
    wbr
    #
    @6
    @58
    clt
    wbr
    #
    @5
    @35
    c2
    cexp
    co
    #
    @57
    clt
    @36
    @5
    @61
    clt
    wbr
    #
    @33
    @36
    cos1bnd
    simpri
    @39
    cc0
    @35
    cle
    wbr
    #
    @36
    @62
    wb
    @45
    cc0
    c2
    cle
    wbr
    @40
    @63
    0le2
    3pos
    c2
    c3
    2re
    3re
    divge0i
    mp2an
    @4
    @35
    @43
    c2
    c3
    2re
    3re
    3ne0
    redivcli
    lt2sqi
    mp2an
    mpbi
    @61
    c2
    c2
    cexp
    co
    #
    @32
    cdiv
    co
    @57
    c2
    c3
    2cn
    3cn
    3ne0
    sqdivi
    @64
    c4
    @32
    c9
    cdiv
    sq2
    sq3
    oveq12i
    eqtri
    breqtri
    @46
    @59
    @60
    wb
    2pos
    @5
    @57
    c2
    @47
    c4
    c9
    4re
    9re
    @16
    redivcli
    2re
    ltmul2i
    ax-mp
    mpbi
    c2
    c4
    cmul
    co
    #
    c9
    cdiv
    co
    @58
    @53
    c2
    c4
    c9
    2cn
    4cn
    9cn
    @16
    divassi
    @65
    c8
    c9
    cdiv
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    oveq1i
    eqtr3i
    breqtri
    @48
    @53
    cr
    wcel
    @42
    @55
    @56
    wb
    @49
    c8
    c9
    8re
    9re
    @16
    redivcli
    1re
    @6
    @53
    c1
    ltsub1
    mp3an
    mpbi
    @53
    @12
    cmin
    co
    #
    @54
    @3
    @12
    c1
    @53
    cmin
    @22
    oveq2i
    @3
    c1
    cneg
    #
    c9
    cdiv
    co
    #
    c8
    c9
    cmin
    co
    #
    c9
    cdiv
    co
    #
    @66
    @51
    @14
    @15
    @3
    @68
    wceq
    ax-1cn
    9cn
    @16
    c1
    c9
    divneg
    mp3an
    @69
    @67
    c9
    cdiv
    c9
    c8
    cmin
    co
    #
    cneg
    @69
    @67
    c9
    c8
    9cn
    8cn
    negsubdi2i
    @71
    c1
    c9
    c8
    c1
    9cn
    8cn
    ax-1cn
    8p1e9
    subaddrii
    negeqi
    eqtr3i
    oveq1i
    c8
    cc
    wcel
    @14
    @19
    @70
    @66
    wceq
    8cn
    9cn
    @20
    c8
    c9
    c9
    divsubdir
    mp3an
    3eqtr2ri
    eqtr3i
    breqtri
    eqbrtri
    pm3.2i
end
