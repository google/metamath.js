include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "cn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "cle.mm"
include "wn.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "cbits.mm"
include "wss.mm"
include "adantr.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "n2dvds1.mm"
include "wceq.mm"
include "caddc.mm"
include "cmul.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "cr.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "sseqtri.mm"
include "wrex.mm"
include "nnssnn0.mm"
include "nn0red.mm"
include "2re.mm"
include "1lt2.mm"
include "expnbnd.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "nn0zd.mm"
include "0red.mm"
include "zred.mm"
include "nn0ge0d.mm"
include "reexpcld.mm"
include "nnred.mm"
include "simpr.mm"
include "oveq2.mm"
include "breq2d.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "lelttrd.mm"
include "ltexp2d.mm"
include "mpbird.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnm1nn0.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "ltm1d.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "infssuzle.mm"
include "mpan.mm"
include "syl5eqbr.mm"
include "syl5bir.mm"
include "mpand.mm"
include "mtod.mm"
include "lenltd.mm"
include "eqbrtrd.mm"
include "1red.mm"
include "crp.mm"
include "2rp.mm"
include "1z.mm"
include "zsubcld.mm"
include "rpexpcld.mm"
include "lemuldivd.mm"
include "cc.mm"
include "2cn.mm"
include "expm1t.mm"
include "breqtrd.mm"
include "ltdivmuld.mm"
include "df-2.mm"
include "syl6breq.mm"
include "wb.mm"
include "rerpdivcld.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "mtbiri.mm"
include "bitsval2.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "elfzolt2.mm"
include "zlem1lt.mm"
include "pm2.65da.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"

theorem bitsfzolem
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume bitsfzo.1: |- ( ph -> N e. NN0 )
  assume bitsfzo.2: |- ( ph -> M e. NN0 )
  assume bitsfzo.3: |- ( ph -> ( bits ` N ) C_ ( 0 ..^ M ) )
  assume bitsfzo.4: |- S = inf ( { n e. NN0 | N < ( 2 ^ n ) } , RR , < )

  disjoint N n
  disjoint m n
  disjoint N m
  disjoint S m
  assert |- ( ph -> N e. ( 0 ..^ ( 2 ^ M ) ) )

  proof
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    c2
    cM
    cexp
    co
    #
    cz
    wcel
    cN
    @1
    clt
    wbr
    #
    cN
    cc0
    @1
    cfzo
    co
    wcel
    wph
    cN
    cn0
    @0
    bitsfzo.1
    nn0uz
    syl6eleq
    wph
    @1
    wph
    c2
    cM
    c2
    cn
    wcel
    #
    wph
    2nn
    a1i
    #
    bitsfzo.2
    nnexpcld
    #
    nnzd
    wph
    @2
    @1
    cN
    cle
    wbr
    #
    wn
    wph
    @6
    cS
    cM
    cle
    wbr
    #
    wph
    @6
    wa
    #
    @7
    cS
    c1
    cmin
    co
    #
    cM
    clt
    wbr
    #
    @8
    @9
    cc0
    cM
    cfzo
    co
    #
    wcel
    @10
    @8
    cN
    cbits
    cfv
    #
    @11
    @9
    wph
    @12
    @11
    wss
    @6
    bitsfzo.3
    adantr
    @8
    @9
    @12
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
    @8
    @17
    c2
    c1
    cdvds
    wbr
    n2dvds1
    @8
    @16
    c1
    c2
    cdvds
    @8
    @16
    c1
    wceq
    #
    c1
    @15
    cle
    wbr
    #
    @15
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @8
    c1
    @14
    cmul
    co
    #
    cN
    cle
    wbr
    @20
    @8
    @23
    @14
    cN
    cle
    @8
    @14
    @8
    @14
    @8
    c2
    @9
    @3
    @8
    2nn
    a1i
    @8
    cS
    cn
    wcel
    #
    @9
    cn0
    wcel
    #
    @8
    cS
    cz
    wcel
    #
    cc0
    cS
    clt
    wbr
    @24
    wph
    @26
    @6
    wph
    cS
    wph
    cN
    c2
    vn
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vn
    cn0
    crab
    #
    cn0
    cS
    @29
    vn
    cn0
    ssrab2
    #
    wph
    cS
    @30
    cr
    clt
    cinf
    #
    @30
    bitsfzo.4
    wph
    @30
    @0
    wss
    #
    @30
    c0
    wne
    #
    @32
    @30
    wcel
    @30
    cn0
    @0
    @31
    nn0uz
    sseqtri
    #
    wph
    @29
    vn
    cn0
    wrex
    #
    @34
    cn
    cn0
    wss
    wph
    @29
    vn
    cn
    wrex
    #
    @36
    nnssnn0
    wph
    cN
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @37
    wph
    cN
    bitsfzo.1
    nn0red
    #
    @39
    wph
    2re
    a1i
    @40
    wph
    1lt2
    a1i
    cN
    c2
    vn
    expnbnd
    syl3anc
    @29
    vn
    cn
    cn0
    ssrexv
    mpsyl
    @29
    vn
    cn0
    rabn0
    sylibr
    @30
    cc0
    infssuzcl
    sylancr
    syl5eqel
    #
    sseldi
    #
    nn0zd
    adantr
    #
    @8
    cc0
    cM
    cS
    @8
    0red
    @8
    cM
    wph
    cM
    cz
    wcel
    #
    @6
    wph
    cM
    bitsfzo.2
    nn0zd
    adantr
    #
    zred
    #
    @8
    cS
    @44
    zred
    #
    @8
    cM
    wph
    cM
    cn0
    wcel
    @6
    bitsfzo.2
    adantr
    #
    nn0ge0d
    @8
    cM
    cS
    clt
    wbr
    #
    @1
    c2
    cS
    cexp
    co
    #
    clt
    wbr
    @8
    @1
    cN
    @51
    @8
    c2
    cM
    @39
    @8
    2re
    a1i
    #
    @49
    reexpcld
    wph
    @38
    @6
    @41
    adantr
    #
    @8
    @51
    wph
    @51
    cn
    wcel
    @6
    wph
    c2
    cS
    @4
    @43
    nnexpcld
    adantr
    nnred
    wph
    @6
    simpr
    @8
    cS
    @30
    wcel
    #
    cN
    @51
    clt
    wbr
    #
    wph
    @54
    @6
    @42
    adantr
    @54
    cS
    cn0
    wcel
    @55
    cN
    c2
    vm
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    @55
    vm
    cS
    cn0
    @30
    @56
    cS
    wceq
    @57
    @51
    cN
    clt
    @56
    cS
    c2
    cexp
    oveq2
    breq2d
    @29
    @58
    vn
    vm
    cn0
    @27
    @56
    wceq
    @28
    @57
    cN
    clt
    @27
    @56
    c2
    cexp
    oveq2
    breq2d
    cbvrabv
    #
    elrab2
    simprbi
    syl
    #
    lelttrd
    @8
    c2
    cM
    cS
    @52
    @46
    @44
    @40
    @8
    1lt2
    a1i
    ltexp2d
    mpbird
    #
    lelttrd
    cS
    elnnz
    sylanbrc
    #
    cS
    nnm1nn0
    syl
    #
    nnexpcld
    #
    nncnd
    mulid2d
    @8
    @14
    cN
    cle
    wbr
    cN
    @14
    clt
    wbr
    #
    wn
    @8
    @65
    cS
    @9
    cle
    wbr
    #
    @8
    @9
    cS
    clt
    wbr
    @66
    wn
    @8
    cS
    @48
    ltm1d
    @8
    @9
    cS
    @8
    @9
    @63
    nn0red
    @48
    ltnled
    mpbid
    @8
    @25
    @65
    @66
    @63
    @25
    @65
    wa
    @9
    @30
    wcel
    #
    @8
    @66
    @58
    @65
    vm
    @9
    cn0
    @30
    @56
    @9
    wceq
    @57
    @14
    cN
    clt
    @56
    @9
    c2
    cexp
    oveq2
    breq2d
    @59
    elrab2
    @67
    @66
    wi
    @8
    @67
    cS
    @32
    @9
    cle
    bitsfzo.4
    @33
    @67
    @32
    @9
    cle
    wbr
    @35
    @9
    @30
    cc0
    infssuzle
    mpan
    syl5eqbr
    a1i
    syl5bir
    mpand
    mtod
    @8
    @14
    cN
    @8
    @14
    @64
    nnred
    @53
    lenltd
    mpbird
    eqbrtrd
    @8
    c1
    cN
    @14
    @8
    1red
    @53
    @8
    c2
    @9
    c2
    crp
    wcel
    @8
    2rp
    a1i
    @8
    cS
    c1
    @44
    c1
    cz
    wcel
    #
    @8
    1z
    a1i
    zsubcld
    rpexpcld
    #
    lemuldivd
    mpbid
    @8
    @15
    c2
    @21
    clt
    @8
    @15
    c2
    clt
    wbr
    cN
    @14
    c2
    cmul
    co
    #
    clt
    wbr
    @8
    cN
    @51
    @70
    clt
    @60
    @8
    c2
    cc
    wcel
    @24
    @51
    @70
    wceq
    2cn
    @62
    c2
    cS
    expm1t
    sylancr
    breqtrd
    @8
    cN
    c2
    @14
    @53
    @52
    @69
    ltdivmuld
    mpbird
    df-2
    syl6breq
    @8
    @15
    cr
    wcel
    @68
    @19
    @20
    @22
    wa
    wb
    @8
    cN
    @14
    @53
    @69
    rerpdivcld
    1z
    @15
    c1
    flbi
    sylancl
    mpbir2and
    breq2d
    mtbiri
    @8
    cN
    cz
    wcel
    #
    @25
    @13
    @18
    wb
    wph
    @71
    @6
    wph
    cN
    bitsfzo.1
    nn0zd
    adantr
    @63
    @9
    cN
    bitsval2
    syl2anc
    mpbird
    sseldd
    @9
    cc0
    cM
    elfzolt2
    syl
    @8
    @26
    @45
    @7
    @10
    wb
    @44
    @46
    cS
    cM
    zlem1lt
    syl2anc
    mpbird
    @8
    @50
    @7
    wn
    @61
    @8
    cM
    cS
    @47
    @48
    ltnled
    mpbid
    pm2.65da
    wph
    cN
    @1
    @41
    wph
    @1
    @5
    nnred
    ltnled
    mpbird
    cN
    cc0
    @1
    elfzo2
    syl3anbrc
end
