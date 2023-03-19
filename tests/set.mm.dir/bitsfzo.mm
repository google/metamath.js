include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cfzo.mm"
include "cbits.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "bitsval.mm"
include "cuz.mm"
include "clt.mm"
include "simp32.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "simp1r.mm"
include "nn0zd.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "reexpcld.mm"
include "simp1l.mm"
include "zred.mm"
include "c1.mm"
include "cmul.mm"
include "cle.mm"
include "recnd.mm"
include "mulid2d.mm"
include "simp33.mm"
include "crp.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "rerpdivcld.mm"
include "1red.mm"
include "ltnled.mm"
include "caddc.mm"
include "0p1e1.mm"
include "breq2i.mm"
include "elfzole1.mm"
include "3ad2ant2.mm"
include "divge0d.mm"
include "wceq.mm"
include "wb.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "2z.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "id.mm"
include "syl5breqr.mm"
include "syl6bir.mm"
include "mpand.mm"
include "syl5bir.mm"
include "sylbird.mm"
include "mt3d.mm"
include "lemuldivd.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "elfzolt2.mm"
include "lelttrd.mm"
include "1lt2.mm"
include "ltexp2d.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "3expia.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "crab.mm"
include "cinf.mm"
include "cneg.mm"
include "cn.mm"
include "cif.mm"
include "simpr.mm"
include "nnred.mm"
include "simpllr.mm"
include "nn0red.mm"
include "max2.mm"
include "syl2anc.mm"
include "simplr.mm"
include "n2dvds1.mm"
include "1z.mm"
include "dvdsnegb.mm"
include "mp2an.mm"
include "mtbi.mm"
include "simplll.mm"
include "2nn.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "nnexpcld.mm"
include "nndivred.mm"
include "zcnd.mm"
include "nncnd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "expne0d.mm"
include "divnegd.mm"
include "max1.mm"
include "uzid.mm"
include "bernneq3.mm"
include "sylancr.mm"
include "ltled.mm"
include "letrd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "nnrpd.mm"
include "ledivmuld.mm"
include "eqbrtrd.mm"
include "lenegcon1d.mm"
include "nngt0d.mm"
include "divgt0d.mm"
include "lt0neg1d.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "syl6breqr.mm"
include "neg1z.mm"
include "mpbir2and.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "bitsval2.mm"
include "sseldd.mm"
include "syl.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "intnand.mm"
include "wo.mm"
include "simpll.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "ord.mm"
include "eqid.mm"
include "bitsfzolem.mm"
include "impbida.mm"

theorem bitsfzo
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let vn: setvar n


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( N e. ( 0 ..^ ( 2 ^ M ) ) <-> ( bits ` N ) C_ ( 0 ..^ M ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cN
    cc0
    c2
    cM
    cexp
    co
    #
    cfzo
    co
    wcel
    #
    cN
    cbits
    cfv
    #
    cc0
    cM
    cfzo
    co
    #
    wss
    #
    @2
    @4
    wa
    #
    vm
    @5
    @6
    vm
    cv
    #
    @5
    wcel
    @0
    @9
    cn0
    wcel
    #
    c2
    cN
    c2
    @9
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    w3a
    #
    @8
    @9
    @6
    wcel
    #
    @9
    cN
    bitsval
    @2
    @4
    @16
    @17
    @2
    @4
    @16
    w3a
    #
    @9
    cc0
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    @9
    cM
    clt
    wbr
    #
    @17
    @18
    @9
    cn0
    @19
    @2
    @4
    @0
    @10
    @15
    simp32
    #
    nn0uz
    syl6eleq
    @18
    cM
    @0
    @1
    @4
    @16
    simp1r
    #
    nn0zd
    #
    @18
    @20
    @11
    @3
    clt
    wbr
    @18
    @11
    cN
    @3
    @18
    c2
    @9
    c2
    cr
    wcel
    @18
    2re
    a1i
    #
    @21
    reexpcld
    #
    @18
    cN
    @0
    @1
    @4
    @16
    simp1l
    zred
    #
    @18
    c2
    cM
    @24
    @22
    reexpcld
    @18
    c1
    @11
    cmul
    co
    #
    @11
    cN
    cle
    @18
    @11
    @18
    @11
    @25
    recnd
    mulid2d
    @18
    @27
    cN
    cle
    wbr
    c1
    @12
    cle
    wbr
    #
    @18
    @28
    @14
    @2
    @4
    @0
    @10
    @15
    simp33
    @18
    @28
    wn
    @12
    c1
    clt
    wbr
    #
    @14
    @18
    @12
    c1
    @18
    cN
    @11
    @26
    @18
    c2
    @9
    c2
    crp
    wcel
    @18
    2rp
    a1i
    @18
    @9
    @21
    nn0zd
    #
    rpexpcld
    #
    rerpdivcld
    #
    @18
    1red
    #
    ltnled
    @29
    @12
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @18
    @14
    @34
    c1
    @12
    clt
    0p1e1
    breq2i
    @18
    cc0
    @12
    cle
    wbr
    #
    @35
    @14
    @18
    cN
    @11
    @26
    @31
    @4
    @2
    cc0
    cN
    cle
    wbr
    @16
    cN
    cc0
    @3
    elfzole1
    3ad2ant2
    divge0d
    @18
    @36
    @35
    wa
    #
    @13
    cc0
    wceq
    #
    @14
    @18
    @12
    cr
    wcel
    cc0
    cz
    wcel
    @38
    @37
    wb
    @32
    0z
    @12
    cc0
    flbi
    sylancl
    @38
    c2
    cc0
    @13
    cdvds
    c2
    cz
    wcel
    #
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    @38
    id
    syl5breqr
    syl6bir
    mpand
    syl5bir
    sylbird
    mt3d
    @18
    c1
    cN
    @11
    @33
    @26
    @31
    lemuldivd
    mpbird
    eqbrtrrd
    @4
    @2
    cN
    @3
    clt
    wbr
    @16
    cN
    cc0
    @3
    elfzolt2
    3ad2ant2
    lelttrd
    @18
    c2
    @9
    cM
    @24
    @30
    @23
    c1
    c2
    clt
    wbr
    @18
    1lt2
    a1i
    ltexp2d
    mpbird
    @9
    cc0
    cM
    elfzo2
    syl3anbrc
    3expia
    syl5bi
    ssrdv
    @2
    @7
    wa
    #
    cN
    c2
    vn
    cv
    cexp
    co
    clt
    wbr
    vn
    cn0
    crab
    cr
    clt
    cinf
    #
    vn
    cM
    cN
    @40
    cN
    cn0
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    @40
    @45
    @43
    @40
    @45
    cM
    @44
    cM
    cle
    wbr
    #
    cM
    @44
    cif
    #
    cle
    wbr
    #
    @40
    @45
    wa
    #
    @44
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @49
    @50
    @44
    @40
    @45
    simpr
    #
    nnred
    #
    @50
    cM
    @0
    @1
    @7
    @45
    simpllr
    #
    nn0red
    #
    @44
    cM
    max2
    syl2anc
    @50
    @48
    cM
    clt
    wbr
    #
    @49
    wn
    @50
    @48
    @6
    wcel
    @57
    @50
    @5
    @6
    @48
    @2
    @7
    @45
    simplr
    @50
    @48
    @5
    wcel
    #
    c2
    cN
    c2
    @48
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    @50
    @62
    c2
    c1
    cneg
    #
    cdvds
    wbr
    #
    c2
    c1
    cdvds
    wbr
    #
    @65
    n2dvds1
    @39
    c1
    cz
    wcel
    @66
    @65
    wb
    2z
    1z
    c2
    c1
    dvdsnegb
    mp2an
    mtbi
    @50
    @61
    @64
    c2
    cdvds
    @50
    @61
    @64
    wceq
    #
    @64
    @60
    cle
    wbr
    #
    @60
    @64
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @50
    @60
    c1
    @50
    cN
    @59
    @50
    cN
    @0
    @1
    @7
    @45
    simplll
    #
    zred
    @50
    c2
    @48
    c2
    cn
    wcel
    @50
    2nn
    a1i
    @50
    @47
    cM
    @44
    cn0
    @55
    @50
    @44
    @53
    nnnn0d
    ifcld
    #
    nnexpcld
    #
    nndivred
    #
    @50
    1red
    #
    @50
    @60
    cneg
    #
    @44
    @59
    cdiv
    co
    #
    c1
    cle
    @50
    cN
    @59
    @50
    cN
    @71
    zcnd
    @50
    @59
    @73
    nncnd
    #
    @50
    c2
    @48
    @50
    2cnd
    c2
    cc0
    wne
    @50
    2ne0
    a1i
    @50
    @48
    @72
    nn0zd
    expne0d
    divnegd
    #
    @50
    @77
    c1
    cle
    wbr
    @44
    @59
    c1
    cmul
    co
    #
    cle
    wbr
    @50
    @44
    @59
    @80
    cle
    @50
    @44
    @48
    @59
    @54
    @50
    @48
    @72
    nn0red
    #
    @50
    @59
    @73
    nnred
    #
    @50
    @51
    @52
    @44
    @48
    cle
    wbr
    @54
    @56
    @44
    cM
    max1
    syl2anc
    @50
    @48
    @59
    @81
    @82
    @50
    c2
    c2
    cuz
    cfv
    wcel
    #
    @48
    cn0
    wcel
    #
    @48
    @59
    clt
    wbr
    @39
    @83
    2z
    c2
    uzid
    ax-mp
    @72
    c2
    @48
    bernneq3
    sylancr
    ltled
    letrd
    @50
    @59
    @78
    mulid1d
    breqtrrd
    @50
    @44
    c1
    @59
    @54
    @75
    @50
    @59
    @73
    nnrpd
    ledivmuld
    mpbird
    eqbrtrd
    lenegcon1d
    @50
    @60
    cc0
    @69
    clt
    @50
    @60
    cc0
    clt
    wbr
    cc0
    @76
    clt
    wbr
    @50
    cc0
    @77
    @76
    clt
    @50
    @44
    @59
    @54
    @82
    @50
    @44
    @53
    nngt0d
    @50
    @59
    @73
    nngt0d
    divgt0d
    @79
    breqtrrd
    @50
    @60
    @74
    lt0neg1d
    mpbird
    c1
    @64
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    syl6breqr
    @50
    @60
    cr
    wcel
    @64
    cz
    wcel
    @67
    @68
    @70
    wa
    wb
    @74
    neg1z
    @60
    @64
    flbi
    sylancl
    mpbir2and
    breq2d
    mtbiri
    @50
    @0
    @84
    @58
    @63
    wb
    @71
    @72
    @48
    cN
    bitsval2
    syl2anc
    mpbird
    sseldd
    @48
    cc0
    cM
    elfzolt2
    syl
    @50
    @48
    cM
    @81
    @56
    ltnled
    mpbid
    pm2.65da
    intnand
    @40
    @42
    @46
    @40
    @0
    @42
    @46
    wo
    @0
    @1
    @7
    simpll
    cN
    elznn0nn
    sylib
    ord
    mt3d
    @0
    @1
    @7
    simplr
    @2
    @7
    simpr
    @41
    eqid
    bitsfzolem
    impbida
end
