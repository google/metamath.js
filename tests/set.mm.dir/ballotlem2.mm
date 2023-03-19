include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cbc.mm"
include "cdiv.mm"
include "chash.mm"
include "cpw.mm"
include "wceq.mm"
include "wss.mm"
include "ssrab2.mm"
include "ballotlemoex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "c2.mm"
include "cfz.mm"
include "wa.mm"
include "cab.mm"
include "an32.mm"
include "cuz.mm"
include "2eluzge1.mm"
include "fzss1.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sseli.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "1lt2.mm"
include "1re.mm"
include "2re.mm"
include "ltnlei.mm"
include "elfzle1.mm"
include "mto.mm"
include "elelpwi.mm"
include "ancom.mm"
include "mtbi.mm"
include "imnani.mm"
include "jca.mm"
include "cin.mm"
include "ssin.mm"
include "wo.mm"
include "wb.mm"
include "1le2.mm"
include "1p1e2.mm"
include "cn.mm"
include "nnge1.mm"
include "nnrei.mm"
include "le2addi.mm"
include "mp2an.mm"
include "eqbrtrri.mm"
include "readdcli.mm"
include "letri.mm"
include "cz.mm"
include "1z.mm"
include "nnaddcl.mm"
include "nnzi.mm"
include "eluz.mm"
include "elfzp12.mm"
include "biimpi.mm"
include "orcanai.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "ss2abi.mm"
include "inab.mm"
include "abid2.mm"
include "ineq1i.mm"
include "eqtr3i.mm"
include "3sstr3i.mm"
include "sstr.mm"
include "mpan2.mm"
include "sylbi.mm"
include "selpw.mm"
include "wi.mm"
include "wal.mm"
include "ssab.mm"
include "wex.mm"
include "df-ex.mm"
include "bicomi.mm"
include "con1bii.mm"
include "df-clel.mm"
include "notbii.mm"
include "imnang.mm"
include "albii.mm"
include "bitr4i.mm"
include "3bitr4ri.mm"
include "bitr2i.mm"
include "anbi12i.mm"
include "3imtr4i.mm"
include "impbii.mm"
include "anbi1i.mm"
include "rabeq2i.mm"
include "3bitr4i.mm"
include "abbii.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "fveq2i.mm"
include "cfn.mm"
include "fzfi.mm"
include "hashbc.mm"
include "cneg.mm"
include "2z.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "hashfz.mm"
include "cc.mm"
include "nncni.mm"
include "addcli.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "subadd23.mm"
include "mp3an.mm"
include "negsubdi2i.mm"
include "2m1e1.mm"
include "negeqi.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "negsubi.mm"
include "eqtri.mm"
include "ballotlem1.mm"
include "oveq12i.mm"
include "cc0.mm"
include "0le1.mm"
include "0re.mm"
include "cr.mm"
include "crp.mm"
include "nngt0i.mm"
include "elrpii.mm"
include "ltaddrp.mm"
include "w3a.mm"
include "0z.mm"
include "elfzm11.mm"
include "mpbir3an.mm"
include "bcm1n.mm"
include "pncan2.mm"

theorem ballotlem2
  let vx: setvar x
  let cP: class P
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )

  disjoint M c
  disjoint N c
  disjoint c x
  disjoint O c
  disjoint O x
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint c i
  disjoint M i
  disjoint N i
  disjoint i x
  disjoint O i
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  assert |- ( P ` { c e. O | -. 1 e. c } ) = ( N / ( M + N ) )

  proof
    c1
    vc
    cv
    #
    wcel
    #
    wn
    #
    vc
    cO
    crab
    #
    cP
    cfv
    #
    cM
    cN
    caddc
    co
    #
    c1
    cmin
    co
    #
    cM
    cbc
    co
    #
    @5
    cM
    cbc
    co
    #
    cdiv
    co
    #
    @5
    cM
    cmin
    co
    #
    @5
    cdiv
    co
    #
    cN
    @5
    cdiv
    co
    @4
    @3
    chash
    cfv
    #
    cO
    chash
    cfv
    #
    cdiv
    co
    #
    @9
    @3
    cO
    cpw
    #
    wcel
    #
    @4
    @14
    wceq
    @16
    @3
    cO
    wss
    @2
    vc
    cO
    ssrab2
    @3
    cO
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemoex
    elpw2
    mpbir
    vx
    @3
    vx
    cv
    #
    chash
    cfv
    #
    @13
    cdiv
    co
    @14
    @15
    cP
    @17
    @3
    wceq
    @18
    @12
    @13
    cdiv
    @17
    @3
    chash
    fveq2
    oveq1d
    ballotth.p
    @12
    @13
    cdiv
    ovex
    fvmpt
    ax-mp
    @12
    @7
    @13
    @8
    cdiv
    @0
    chash
    cfv
    cM
    wceq
    #
    vc
    c2
    @5
    cfz
    co
    #
    cpw
    #
    crab
    #
    chash
    cfv
    #
    @12
    @7
    @22
    @3
    chash
    @0
    @21
    wcel
    #
    @19
    wa
    #
    vc
    cab
    @0
    cO
    wcel
    #
    @2
    wa
    #
    vc
    cab
    @22
    @3
    @25
    @27
    vc
    @0
    c1
    @5
    cfz
    co
    #
    cpw
    #
    wcel
    #
    @2
    wa
    #
    @19
    wa
    @30
    @19
    wa
    #
    @2
    wa
    @25
    @27
    @30
    @2
    @19
    an32
    @24
    @31
    @19
    @24
    @31
    @24
    @30
    @2
    @21
    @29
    @0
    @20
    @28
    wss
    #
    @21
    @29
    wss
    c2
    c1
    cuz
    cfv
    #
    wcel
    @33
    2eluzge1
    c2
    c1
    @5
    fzss1
    ax-mp
    @20
    @28
    sspwb
    mpbi
    sseli
    @24
    @1
    @1
    @24
    wa
    #
    @24
    @1
    wa
    @35
    c1
    @20
    wcel
    #
    @36
    c2
    c1
    cle
    wbr
    #
    c1
    c2
    clt
    wbr
    @37
    wn
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    c1
    c2
    @5
    elfzle1
    mto
    c1
    @0
    @20
    elelpwi
    mto
    @1
    @24
    ancom
    mtbi
    imnani
    jca
    @0
    @28
    wss
    #
    @0
    vi
    cv
    #
    c1
    wceq
    #
    wn
    #
    vi
    cab
    #
    wss
    #
    wa
    #
    @0
    @20
    wss
    #
    @31
    @24
    @44
    @0
    @28
    @42
    cin
    #
    wss
    #
    @45
    @0
    @28
    @42
    ssin
    @47
    @46
    @20
    wss
    @45
    @39
    @28
    wcel
    #
    @41
    wa
    #
    vi
    cab
    #
    @39
    @20
    wcel
    #
    vi
    cab
    @46
    @20
    @49
    @51
    vi
    @49
    @39
    c1
    c1
    caddc
    co
    #
    @5
    cfz
    co
    #
    @20
    @48
    @40
    @39
    @53
    wcel
    #
    @48
    @40
    @54
    wo
    #
    @5
    @34
    wcel
    #
    @48
    @55
    wb
    @56
    c1
    @5
    cle
    wbr
    #
    c1
    c2
    cle
    wbr
    c2
    @5
    cle
    wbr
    #
    @57
    1le2
    @52
    c2
    @5
    cle
    1p1e2
    c1
    cM
    cle
    wbr
    #
    c1
    cN
    cle
    wbr
    #
    @52
    @5
    cle
    wbr
    cM
    cn
    wcel
    #
    @59
    ballotth.m
    cM
    nnge1
    ax-mp
    #
    cN
    cn
    wcel
    #
    @60
    ballotth.n
    cN
    nnge1
    ax-mp
    c1
    c1
    cM
    cN
    1re
    1re
    cM
    ballotth.m
    nnrei
    #
    cN
    ballotth.n
    nnrei
    #
    le2addi
    mp2an
    eqbrtrri
    #
    c1
    c2
    @5
    1re
    2re
    cM
    cN
    @64
    @65
    readdcli
    letri
    mp2an
    c1
    cz
    wcel
    @5
    cz
    wcel
    #
    @56
    @57
    wb
    1z
    @5
    @61
    @63
    @5
    cn
    wcel
    #
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    #
    nnzi
    #
    c1
    @5
    eluz
    mp2an
    mpbir
    @39
    c1
    @5
    elfzp12
    ax-mp
    biimpi
    orcanai
    @52
    c2
    @5
    cfz
    1p1e2
    oveq1i
    syl6eleq
    ss2abi
    @48
    vi
    cab
    #
    @42
    cin
    @50
    @46
    @48
    @41
    vi
    inab
    @71
    @28
    @42
    vi
    @28
    abid2
    ineq1i
    eqtr3i
    vi
    @20
    abid2
    3sstr3i
    @0
    @46
    @20
    sstr
    mpan2
    sylbi
    @30
    @38
    @2
    @43
    vc
    @28
    selpw
    @43
    @39
    @0
    wcel
    #
    @41
    wi
    vi
    wal
    #
    @2
    @41
    vi
    @0
    ssab
    @40
    @72
    wa
    #
    vi
    wex
    #
    wn
    @74
    wn
    #
    vi
    wal
    #
    @2
    @73
    @77
    @75
    @75
    @77
    wn
    @74
    vi
    df-ex
    bicomi
    con1bii
    @1
    @75
    vi
    c1
    @0
    df-clel
    notbii
    @73
    @72
    @40
    wa
    #
    wn
    #
    vi
    wal
    @77
    @72
    @40
    vi
    imnang
    @76
    @79
    vi
    @74
    @78
    @40
    @72
    ancom
    notbii
    albii
    bitr4i
    3bitr4ri
    bitr2i
    anbi12i
    vc
    @20
    selpw
    3imtr4i
    impbii
    anbi1i
    @26
    @32
    @2
    @19
    vc
    cO
    @29
    ballotth.o
    rabeq2i
    anbi1i
    3bitr4i
    abbii
    @19
    vc
    @21
    df-rab
    @2
    vc
    cO
    df-rab
    3eqtr4i
    fveq2i
    @20
    chash
    cfv
    #
    cM
    cbc
    co
    #
    @23
    @7
    @20
    cfn
    wcel
    cM
    cz
    wcel
    #
    @81
    @23
    wceq
    c2
    @5
    fzfi
    cM
    ballotth.m
    nnzi
    #
    vc
    @20
    cM
    hashbc
    mp2an
    @80
    @6
    cM
    cbc
    @80
    @5
    c1
    cneg
    #
    caddc
    co
    #
    @6
    @80
    @5
    c2
    cmin
    co
    c1
    caddc
    co
    #
    @5
    c1
    c2
    cmin
    co
    #
    caddc
    co
    #
    @85
    @5
    c2
    cuz
    cfv
    wcel
    #
    @80
    @86
    wceq
    @89
    @67
    @58
    @70
    @66
    c2
    @5
    2z
    eluz1i
    mpbir2an
    c2
    @5
    hashfz
    ax-mp
    @5
    cc
    wcel
    c2
    cc
    wcel
    c1
    cc
    wcel
    @86
    @88
    wceq
    cM
    cN
    cM
    ballotth.m
    nncni
    #
    cN
    ballotth.n
    nncni
    #
    addcli
    #
    2cn
    ax-1cn
    @5
    c2
    c1
    subadd23
    mp3an
    @87
    @84
    @5
    caddc
    c2
    c1
    cmin
    co
    #
    cneg
    @87
    @84
    c2
    c1
    2cn
    ax-1cn
    negsubdi2i
    @93
    c1
    2m1e1
    negeqi
    eqtr3i
    oveq2i
    3eqtri
    @5
    c1
    @92
    ax-1cn
    negsubi
    eqtri
    oveq1i
    eqtr3i
    eqtr3i
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlem1
    oveq12i
    eqtri
    cM
    cc0
    @6
    cfz
    co
    wcel
    #
    @68
    @9
    @11
    wceq
    @94
    @82
    cc0
    cM
    cle
    wbr
    #
    cM
    @5
    clt
    wbr
    #
    @83
    cc0
    c1
    cle
    wbr
    @59
    @95
    0le1
    @62
    cc0
    c1
    cM
    0re
    1re
    @64
    letri
    mp2an
    cM
    cr
    wcel
    cN
    crp
    wcel
    @96
    @64
    cN
    @65
    cN
    ballotth.n
    nngt0i
    elrpii
    cM
    cN
    ltaddrp
    mp2an
    cc0
    cz
    wcel
    @67
    @94
    @82
    @95
    @96
    w3a
    wb
    0z
    @70
    cM
    cc0
    @5
    elfzm11
    mp2an
    mpbir3an
    @69
    cM
    @5
    bcm1n
    mp2an
    @10
    cN
    @5
    cdiv
    cM
    cc
    wcel
    cN
    cc
    wcel
    @10
    cN
    wceq
    @90
    @91
    cM
    cN
    pncan2
    mp2an
    oveq1i
    3eqtri
end
