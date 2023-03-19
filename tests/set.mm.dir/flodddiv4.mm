include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "c4.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "oveq1.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "2cnd.mm"
include "zcn.mm"
include "mulcld.mm"
include "1cnd.mm"
include "4cn.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "divdir.mm"
include "syl3anc.mm"
include "2t2e4.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "2ne0.mm"
include "divcan5d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "iftrue.mm"
include "adantr.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "1re.mm"
include "0le1.mm"
include "4re.mm"
include "4pos.mm"
include "divge0.mm"
include "mp4an.mm"
include "1lt4.mm"
include "wb.mm"
include "recgt1.mm"
include "mp2an.mm"
include "mpbi.mm"
include "2z.mm"
include "id.mm"
include "dvdsval2.mm"
include "biimpac.mm"
include "cn.mm"
include "4nn.mm"
include "nnrecre.mm"
include "ax-mp.mm"
include "flbi2.mm"
include "sylancl.mm"
include "mpbiri.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "cv.mm"
include "wrex.mm"
include "odd2np1.mm"
include "wi.mm"
include "c3.mm"
include "ax-1cn.mm"
include "2cnne0.mm"
include "divcan5.mm"
include "mp3an.mm"
include "2t1e2.mm"
include "oveq12i.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "2cn.mm"
include "divdiri.mm"
include "2p1e3.mm"
include "3eqtr2i.mm"
include "3re.mm"
include "0re.mm"
include "3pos.mm"
include "ltleii.mm"
include "3lt4.mm"
include "crp.mm"
include "nnrp.mm"
include "divlt1lt.mm"
include "mpbir.mm"
include "redivcli.mm"
include "mpan2.mm"
include "eqcoms.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "divcan3d.mm"
include "halfcn.mm"
include "reccli.mm"
include "addassd.mm"
include "pncan1.mm"
include "syl.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "adantl.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "impcom.mm"
include "pm2.61ian.mm"
include "eqcomd.mm"

theorem flodddiv4
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N = ( ( 2 x. M ) + 1 ) ) -> ( |_ ` ( N / 4 ) ) = if ( 2 || M , ( M / 2 ) , ( ( M - 1 ) / 2 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    c2
    cM
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
    cM
    c2
    cdiv
    co
    #
    c1
    c4
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    c2
    cM
    cdvds
    wbr
    #
    @6
    cM
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cif
    #
    @4
    @5
    @8
    cfl
    @3
    @0
    @5
    @2
    c4
    cdiv
    co
    #
    @8
    cN
    @2
    c4
    cdiv
    oveq1
    @0
    @14
    @1
    c4
    cdiv
    co
    #
    @7
    caddc
    co
    #
    @8
    @0
    @1
    cc
    wcel
    c1
    cc
    wcel
    #
    c4
    cc
    wcel
    #
    c4
    cc0
    wne
    #
    wa
    #
    @14
    @16
    wceq
    @0
    c2
    cM
    @0
    2cnd
    #
    cM
    zcn
    #
    mulcld
    @0
    1cnd
    @20
    @0
    @18
    @19
    4cn
    4ne0
    pm3.2i
    a1i
    @1
    c1
    c4
    divdir
    syl3anc
    @0
    @15
    @6
    @7
    caddc
    @0
    @15
    @1
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @6
    @0
    c4
    @23
    @1
    cdiv
    c4
    @23
    wceq
    @0
    @23
    c4
    2t2e4
    eqcomi
    a1i
    oveq2d
    @0
    cM
    c2
    c2
    @22
    @21
    @21
    c2
    cc0
    wne
    #
    @0
    2ne0
    a1i
    #
    @25
    divcan5d
    eqtrd
    oveq1d
    eqtrd
    sylan9eqr
    fveq2d
    @0
    @9
    @13
    wceq
    @3
    @0
    @13
    @9
    @10
    @0
    @13
    @9
    wceq
    @10
    @0
    wa
    #
    @13
    @6
    @9
    @10
    @13
    @6
    wceq
    @0
    @10
    @6
    @12
    iftrue
    adantr
    @26
    @9
    @6
    wceq
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    c1
    clt
    wbr
    #
    wa
    #
    @28
    @29
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    c4
    cr
    wcel
    #
    cc0
    c4
    clt
    wbr
    #
    @28
    1re
    0le1
    4re
    4pos
    c1
    c4
    divge0
    mp4an
    c1
    c4
    clt
    wbr
    #
    @29
    1lt4
    @31
    @32
    @33
    @29
    wb
    4re
    4pos
    c4
    recgt1
    mp2an
    mpbi
    pm3.2i
    @26
    @6
    cz
    wcel
    #
    @7
    cr
    wcel
    #
    @27
    @30
    wb
    @0
    @10
    @34
    @0
    c2
    cz
    wcel
    #
    @24
    @0
    @10
    @34
    wb
    @36
    @0
    2z
    a1i
    @25
    @0
    id
    c2
    cM
    dvdsval2
    syl3anc
    biimpac
    c4
    cn
    wcel
    #
    @35
    4nn
    c4
    nnrecre
    ax-mp
    @7
    @6
    flbi2
    sylancl
    mpbiri
    eqtr4d
    @10
    wn
    #
    @0
    wa
    @13
    @12
    @9
    @38
    @13
    @12
    wceq
    @0
    @10
    @6
    @12
    iffalse
    adantr
    @0
    @38
    @12
    @9
    wceq
    #
    @0
    @38
    c2
    vx
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cM
    wceq
    #
    vx
    cz
    wrex
    @39
    vx
    cM
    odd2np1
    @0
    @43
    @39
    vx
    cz
    @40
    cz
    wcel
    #
    @43
    @39
    wi
    @0
    @44
    @43
    @39
    @44
    @43
    wa
    #
    @40
    c1
    c2
    cdiv
    co
    #
    @7
    caddc
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @40
    @9
    @12
    @44
    @49
    @40
    wceq
    @43
    @44
    @49
    @40
    c3
    c4
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @40
    @44
    @48
    @51
    cfl
    @44
    @47
    @50
    @40
    caddc
    @47
    @50
    wceq
    @44
    @47
    c2
    c4
    cdiv
    co
    #
    @7
    caddc
    co
    c2
    c1
    caddc
    co
    #
    c4
    cdiv
    co
    @50
    @46
    @53
    @7
    caddc
    c2
    c1
    cmul
    co
    #
    @23
    cdiv
    co
    #
    @46
    @53
    @17
    c2
    cc
    wcel
    @24
    wa
    #
    @57
    @56
    @46
    wceq
    ax-1cn
    2cnne0
    2cnne0
    c1
    c2
    c2
    divcan5
    mp3an
    @55
    c2
    @23
    c4
    cdiv
    2t1e2
    2t2e4
    oveq12i
    eqtr3i
    oveq1i
    c2
    c1
    c4
    2cn
    ax-1cn
    4cn
    4ne0
    divdiri
    @54
    c3
    c4
    cdiv
    2p1e3
    oveq1i
    3eqtr2i
    a1i
    oveq2d
    fveq2d
    @44
    @52
    @40
    wceq
    #
    cc0
    @50
    cle
    wbr
    #
    @50
    c1
    clt
    wbr
    #
    wa
    #
    @59
    @60
    c3
    cr
    wcel
    #
    cc0
    c3
    cle
    wbr
    @31
    @32
    @59
    3re
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    4re
    4pos
    c3
    c4
    divge0
    mp4an
    @60
    c3
    c4
    clt
    wbr
    #
    3lt4
    @62
    c4
    crp
    wcel
    #
    @60
    @63
    wb
    3re
    @37
    @64
    4nn
    c4
    nnrp
    ax-mp
    c3
    c4
    divlt1lt
    mp2an
    mpbir
    pm3.2i
    @44
    @50
    cr
    wcel
    @58
    @61
    wb
    c3
    c4
    3re
    4re
    4ne0
    redivcli
    @50
    @40
    flbi2
    mpan2
    mpbiri
    eqtrd
    adantr
    @45
    @8
    @48
    cfl
    @45
    @8
    @40
    @46
    caddc
    co
    #
    @7
    caddc
    co
    #
    @48
    @45
    @6
    @65
    @7
    caddc
    @43
    @44
    @6
    @42
    c2
    cdiv
    co
    #
    @65
    @6
    @67
    wceq
    cM
    @42
    cM
    @42
    c2
    cdiv
    oveq1
    eqcoms
    @44
    @67
    @41
    c2
    cdiv
    co
    #
    @46
    caddc
    co
    #
    @65
    @44
    @41
    cc
    wcel
    #
    @17
    @57
    @67
    @69
    wceq
    @44
    @41
    @44
    c2
    @40
    @36
    @44
    2z
    a1i
    @44
    id
    zmulcld
    zcnd
    #
    @44
    1cnd
    @57
    @44
    2cnne0
    a1i
    @41
    c1
    c2
    divdir
    syl3anc
    @44
    @68
    @40
    @46
    caddc
    @44
    @40
    c2
    @40
    zcn
    #
    @44
    2cnd
    @24
    @44
    2ne0
    a1i
    divcan3d
    #
    oveq1d
    eqtrd
    sylan9eqr
    oveq1d
    @44
    @66
    @48
    wceq
    @43
    @44
    @40
    @46
    @7
    @72
    @46
    cc
    wcel
    @44
    halfcn
    a1i
    @7
    cc
    wcel
    @44
    c4
    4cn
    4ne0
    reccli
    a1i
    addassd
    adantr
    eqtrd
    fveq2d
    @45
    @12
    @68
    @40
    @45
    @11
    @41
    c2
    cdiv
    @43
    @44
    @11
    @42
    c1
    cmin
    co
    #
    @41
    @11
    @74
    wceq
    cM
    @42
    cM
    @42
    c1
    cmin
    oveq1
    eqcoms
    @44
    @70
    @74
    @41
    wceq
    @71
    @41
    pncan1
    syl
    sylan9eqr
    oveq1d
    @44
    @68
    @40
    wceq
    @43
    @73
    adantr
    eqtrd
    3eqtr4rd
    ex
    adantl
    rexlimdva
    sylbid
    impcom
    eqtrd
    pm2.61ian
    eqcomd
    adantr
    eqtrd
end
