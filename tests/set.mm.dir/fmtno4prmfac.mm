include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfl.mm"
include "cle.mm"
include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "c9.mm"
include "c3.mm"
include "w3o.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "4z.mm"
include "2re.mm"
include "4re.mm"
include "2lt4.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "fmtnoprmfac2.mm"
include "mp3an1.mm"
include "wo.mm"
include "cfzo.mm"
include "cun.mm"
include "elnnuz.mm"
include "4nn.mm"
include "nnuz.mm"
include "eleqtri.mm"
include "fzouzsplit.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "elun.mm"
include "ctp.mm"
include "fzo1to4tp.mm"
include "vex.mm"
include "eltp.mm"
include "bitri.mm"
include "orbi1i.mm"
include "3bitri.mm"
include "4p2e6.mm"
include "oveq2i.mm"
include "2exp6.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eqeq2i.mm"
include "simpl.mm"
include "oveq1.mm"
include "6nn0.mm"
include "4nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "4p1e5.mm"
include "eqid.mm"
include "decsuc.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "cc0.mm"
include "c8.mm"
include "2nn0.mm"
include "6cn.mm"
include "2cn.mm"
include "6t2e12.mm"
include "mulcomli.mm"
include "eqcomi.mm"
include "4cn.mm"
include "4t2e8.mm"
include "decmul10add.mm"
include "1nn0.mm"
include "8nn0.mm"
include "8p1e9.mm"
include "0nn0.mm"
include "8cn.mm"
include "addid2i.mm"
include "decaddi.mm"
include "3nn0.mm"
include "6t3e18.mm"
include "3cn.mm"
include "mulcomi.mm"
include "eqtr3i.mm"
include "4t3e12.mm"
include "9nn0.mm"
include "2p1e3.mm"
include "decadd.mm"
include "3orim123d.mm"
include "a1i.mm"
include "com13.mm"
include "fmtno4sqrt.mm"
include "breq2i.mm"
include "wb.mm"
include "breq1.mm"
include "clt.mm"
include "wn.mm"
include "w3a.mm"
include "6t4e24.mm"
include "4t4e16.mm"
include "decmul2c.mm"
include "cr.mm"
include "zre.mm"
include "nn0rei.mm"
include "decnncl.mm"
include "nngt0i.mm"
include "pm3.2i.mm"
include "lemul1.mm"
include "mp3an2i.mm"
include "biimpa.mm"
include "syl5eqbrr.mm"
include "5nn0.mm"
include "nn0zi.mm"
include "id.mm"
include "zmulcld.mm"
include "adantr.mm"
include "zleltp1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "3adant1.mm"
include "sylbi.mm"
include "eluzelre.mm"
include "remulcld.mm"
include "peano2re.mm"
include "syl.mm"
include "ltnled.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "jaoi.mm"
include "com12.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "3impia.mm"

theorem fmtno4prmfac
  let cP: class P
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ P || ( FermatNo ` 4 ) /\ P <_ ( |_ ` ( sqrt ` ( FermatNo ` 4 ) ) ) ) -> ( P = ; 6 5 \/ P = ; ; 1 2 9 \/ P = ; ; 1 9 3 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c4
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    cP
    @1
    csqrt
    cfv
    cfl
    cfv
    #
    cle
    wbr
    #
    cP
    c6
    c5
    cdc
    #
    wceq
    #
    cP
    c1
    c2
    cdc
    #
    c9
    cdc
    #
    wceq
    #
    cP
    c1
    c9
    cdc
    #
    c3
    cdc
    #
    wceq
    #
    w3o
    #
    @0
    @2
    wa
    #
    cP
    vk
    cv
    #
    c2
    c4
    c2
    caddc
    co
    #
    cexp
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
    vk
    cn
    wrex
    #
    @4
    @13
    wi
    #
    c4
    c2
    cuz
    cfv
    wcel
    #
    @0
    @2
    @21
    @23
    c2
    cz
    wcel
    c4
    cz
    wcel
    #
    c2
    c4
    cle
    wbr
    2z
    4z
    c2
    c4
    2re
    4re
    2lt4
    ltleii
    c2
    c4
    eluz2
    mpbir3an
    cP
    vk
    c4
    fmtnoprmfac2
    mp3an1
    @14
    @20
    @22
    vk
    cn
    @15
    cn
    wcel
    #
    @14
    @20
    @22
    wi
    #
    @25
    @15
    c1
    wceq
    #
    @15
    c2
    wceq
    #
    @15
    c3
    wceq
    #
    w3o
    #
    @15
    c4
    cuz
    cfv
    #
    wcel
    #
    wo
    #
    @14
    @26
    wi
    @25
    @15
    c1
    cuz
    cfv
    #
    wcel
    @15
    c1
    c4
    cfzo
    co
    #
    @31
    cun
    #
    wcel
    #
    @33
    @15
    elnnuz
    @34
    @36
    @15
    c4
    @34
    wcel
    @34
    @36
    wceq
    c4
    cn
    @34
    4nn
    nnuz
    eleqtri
    c1
    c4
    fzouzsplit
    ax-mp
    eleq2i
    @37
    @15
    @35
    wcel
    #
    @32
    wo
    @33
    @15
    @35
    @31
    elun
    @38
    @30
    @32
    @38
    @15
    c1
    c2
    c3
    ctp
    #
    wcel
    @30
    @35
    @39
    @15
    fzo1to4tp
    eleq2i
    @15
    c1
    c2
    c3
    vk
    vex
    eltp
    bitri
    orbi1i
    bitri
    3bitri
    @33
    @14
    @26
    @20
    cP
    @15
    c6
    c4
    cdc
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
    @33
    @14
    wa
    @22
    @19
    @42
    cP
    @18
    @41
    c1
    caddc
    @17
    @40
    @15
    cmul
    @17
    c2
    c6
    cexp
    co
    @40
    @16
    c6
    c2
    cexp
    4p2e6
    oveq2i
    2exp6
    eqtri
    oveq2i
    oveq1i
    eqeq2i
    @33
    @43
    @22
    wi
    #
    @14
    @30
    @44
    @32
    @4
    @43
    @30
    @13
    @43
    @30
    @13
    wi
    wi
    @4
    @43
    @27
    @6
    @28
    @9
    @29
    @12
    @43
    @27
    @6
    @43
    @27
    wa
    cP
    @42
    @5
    @43
    @27
    simpl
    @27
    @42
    @5
    wceq
    @43
    @27
    @42
    @40
    c1
    caddc
    co
    @5
    @27
    @41
    @40
    c1
    caddc
    @27
    @41
    c1
    @40
    cmul
    co
    @40
    @15
    c1
    @40
    cmul
    oveq1
    @40
    @40
    c6
    c4
    6nn0
    4nn0
    deccl
    #
    nn0cni
    mulid2i
    syl6eq
    oveq1d
    c6
    c4
    c5
    @40
    6nn0
    4nn0
    4p1e5
    @40
    eqid
    #
    decsuc
    syl6eq
    adantl
    eqtrd
    ex
    @43
    @28
    @9
    @43
    @28
    wa
    cP
    @42
    @8
    @43
    @28
    simpl
    @28
    @42
    @8
    wceq
    @43
    @28
    @42
    @7
    cc0
    cdc
    #
    c8
    caddc
    co
    #
    c1
    caddc
    co
    @8
    @28
    @41
    @48
    c1
    caddc
    @28
    @41
    c2
    @40
    cmul
    co
    @48
    @15
    c2
    @40
    cmul
    oveq1
    c6
    c4
    @7
    c8
    c2
    6nn0
    4nn0
    2nn0
    c2
    c6
    cmul
    co
    @7
    c6
    c2
    @7
    6cn
    2cn
    6t2e12
    mulcomli
    eqcomi
    c2
    c4
    cmul
    co
    c8
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    eqcomi
    decmul10add
    syl6eq
    oveq1d
    @7
    c8
    c9
    @48
    c1
    c2
    1nn0
    2nn0
    deccl
    #
    8nn0
    8p1e9
    @7
    cc0
    c8
    @47
    c8
    @49
    0nn0
    8nn0
    @47
    eqid
    c8
    8cn
    addid2i
    decaddi
    decsuc
    syl6eq
    adantl
    eqtrd
    ex
    @43
    @29
    @12
    @43
    @29
    wa
    cP
    @42
    @11
    @43
    @29
    simpl
    @29
    @42
    @11
    wceq
    @43
    @29
    @42
    c1
    c8
    cdc
    #
    cc0
    cdc
    #
    @7
    caddc
    co
    #
    c1
    caddc
    co
    @11
    @29
    @41
    @52
    c1
    caddc
    @29
    @41
    c3
    @40
    cmul
    co
    @52
    @15
    c3
    @40
    cmul
    oveq1
    c6
    c4
    @50
    @7
    c3
    6nn0
    4nn0
    3nn0
    c6
    c3
    cmul
    co
    @50
    c3
    c6
    cmul
    co
    6t3e18
    c6
    c3
    6cn
    3cn
    mulcomi
    eqtr3i
    c4
    c3
    cmul
    co
    @7
    c3
    c4
    cmul
    co
    4t3e12
    c4
    c3
    4cn
    3cn
    mulcomi
    eqtr3i
    decmul10add
    syl6eq
    oveq1d
    @10
    c2
    c3
    @52
    c1
    c9
    1nn0
    9nn0
    deccl
    2nn0
    2p1e3
    @50
    cc0
    c1
    c2
    @10
    c2
    @51
    @7
    c1
    c8
    1nn0
    8nn0
    deccl
    0nn0
    1nn0
    2nn0
    @51
    eqid
    @7
    eqid
    c1
    c8
    c9
    @50
    1nn0
    8nn0
    8p1e9
    @50
    eqid
    decsuc
    c2
    2cn
    addid2i
    decadd
    decsuc
    syl6eq
    adantl
    eqtrd
    ex
    3orim123d
    a1i
    com13
    @32
    @43
    @22
    @4
    cP
    c2
    c5
    cdc
    #
    c6
    cdc
    #
    cle
    wbr
    #
    @32
    @43
    wa
    #
    @13
    @3
    @54
    cP
    cle
    fmtno4sqrt
    breq2i
    @56
    @55
    @42
    @54
    cle
    wbr
    #
    @13
    @43
    @55
    @57
    wb
    @32
    cP
    @42
    @54
    cle
    breq1
    adantl
    @32
    @57
    @13
    wi
    @43
    @32
    @57
    @13
    @32
    @54
    @42
    clt
    wbr
    #
    @57
    wn
    @32
    @24
    @15
    cz
    wcel
    #
    c4
    @15
    cle
    wbr
    #
    w3a
    @58
    c4
    @15
    eluz2
    @59
    @60
    @58
    @24
    @59
    @60
    wa
    #
    @54
    @41
    cle
    wbr
    #
    @58
    @61
    @54
    c4
    @40
    cmul
    co
    #
    @41
    cle
    c6
    c4
    @53
    c6
    c4
    c1
    @40
    4nn0
    6nn0
    4nn0
    @46
    6nn0
    1nn0
    c2
    c4
    c5
    c4
    c6
    cmul
    co
    2nn0
    4nn0
    4p1e5
    c6
    c4
    c2
    c4
    cdc
    6cn
    4cn
    6t4e24
    mulcomli
    decsuc
    4t4e16
    decmul2c
    @59
    @60
    @63
    @41
    cle
    wbr
    #
    c4
    cr
    wcel
    @59
    @15
    cr
    wcel
    @40
    cr
    wcel
    #
    cc0
    @40
    clt
    wbr
    #
    wa
    #
    @60
    @64
    wb
    4re
    @15
    zre
    @67
    @59
    @65
    @66
    @40
    @45
    nn0rei
    #
    @40
    c6
    c4
    6nn0
    4nn
    decnncl
    nngt0i
    pm3.2i
    a1i
    c4
    @15
    @40
    lemul1
    mp3an2i
    biimpa
    syl5eqbrr
    @61
    @54
    cz
    wcel
    @41
    cz
    wcel
    #
    @62
    @58
    wb
    @54
    @53
    c6
    c2
    c5
    2nn0
    5nn0
    deccl
    6nn0
    deccl
    #
    nn0zi
    @59
    @69
    @60
    @59
    @15
    @40
    @59
    id
    @40
    cz
    wcel
    @59
    @40
    @45
    nn0zi
    a1i
    zmulcld
    adantr
    @54
    @41
    zleltp1
    sylancr
    mpbid
    3adant1
    sylbi
    @32
    @54
    @42
    @54
    cr
    wcel
    @32
    @54
    @70
    nn0rei
    a1i
    @32
    @41
    cr
    wcel
    @42
    cr
    wcel
    @32
    @15
    @40
    c4
    @15
    eluzelre
    @65
    @32
    @68
    a1i
    remulcld
    @41
    peano2re
    syl
    ltnled
    mpbid
    pm2.21d
    adantr
    sylbid
    syl5bi
    ex
    jaoi
    adantr
    syl5bi
    ex
    sylbi
    com12
    rexlimdv
    mpd
    3impia
end
