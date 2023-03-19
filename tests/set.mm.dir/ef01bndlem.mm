include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "c4.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cabs.mm"
include "cexp.mm"
include "caddc.mm"
include "cfa.mm"
include "cmul.mm"
include "cdiv.mm"
include "c6.mm"
include "ci.mm"
include "cc.mm"
include "cn0.mm"
include "ax-icn.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "recnd.mm"
include "mulcl.mm"
include "sylancr.mm"
include "4nn0.mm"
include "eftlcl.mm"
include "sylancl.mm"
include "abscld.mm"
include "reexpcl.mm"
include "cn.mm"
include "4re.mm"
include "readdcli.mm"
include "faccl.mm"
include "ax-mp.mm"
include "4nn.mm"
include "nnmulcli.mm"
include "nndivre.mm"
include "remulcl.mm"
include "6nn.mm"
include "cmpt.mm"
include "eqid.mm"
include "a1i.mm"
include "wceq.mm"
include "absmul.mm"
include "absi.mm"
include "oveq1i.mm"
include "crp.mm"
include "simp2bi.mm"
include "elrpd.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "syl.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "simp3bi.mm"
include "eqbrtrd.mm"
include "eftlub.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "c5.mm"
include "c2.mm"
include "c3.mm"
include "3pos.mm"
include "0re.mm"
include "3re.mm"
include "5re.mm"
include "ltadd1i.mm"
include "mpbi.mm"
include "5cn.mm"
include "addid2i.mm"
include "c8.mm"
include "cu2.mm"
include "5p3e8.mm"
include "3nn.mm"
include "nncni.mm"
include "addcomi.mm"
include "3eqtr2ri.mm"
include "3brtr3i.mm"
include "2re.mm"
include "1le2.mm"
include "cz.mm"
include "4z.mm"
include "3lt4.mm"
include "ltleii.mm"
include "nnzi.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "leexp2a.mm"
include "mp3an.mm"
include "8re.mm"
include "eqeltri.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "nnrei.mm"
include "ltletri.mm"
include "6re.mm"
include "remulcli.mm"
include "6pos.mm"
include "nngt0i.mm"
include "mulgt0ii.mm"
include "ltdiv1ii.mm"
include "df-5.mm"
include "df-4.mm"
include "fveq2i.mm"
include "3nn0.mm"
include "facp1.mm"
include "sq2.mm"
include "eqtr2i.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "fac3.mm"
include "6cn.mm"
include "recni.mm"
include "mulassi.mm"
include "3eqtr3i.mm"
include "2p2e4.mm"
include "2cn.mm"
include "2nn0.mm"
include "expadd.mm"
include "eqtr3i.mm"
include "oveq12i.mm"
include "mulid2i.mm"
include "nnne0i.mm"
include "dividi.mm"
include "ax-1cn.mm"
include "gt0ne0ii.mm"
include "divmuldivi.mm"
include "rereccli.mm"
include "mulid1i.mm"
include "rpexpcl.mm"
include "wa.mm"
include "elrp.mm"
include "ltmul2.mm"
include "mp3an12.mm"
include "sylbi.mm"
include "mpbii.mm"
include "wne.mm"
include "divrec.mm"
include "mp3an23.mm"
include "breqtrrd.mm"
include "lelttrd.mm"

theorem ef01bndlem
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  assume ef01bnd.1: |- F = ( n e. NN0 |-> ( ( ( _i x. A ) ^ n ) / ( ! ` n ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  assert |- ( A e. ( 0 (,] 1 ) -> ( abs ` sum_ k e. ( ZZ>= ` 4 ) ( F ` k ) ) < ( ( A ^ 4 ) / 6 ) )

  proof
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    c4
    cuz
    cfv
    vk
    cv
    cF
    cfv
    vk
    csu
    #
    cabs
    cfv
    #
    cA
    c4
    cexp
    co
    #
    c4
    c1
    caddc
    co
    #
    c4
    cfa
    cfv
    #
    c4
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @3
    c6
    cdiv
    co
    #
    @0
    @1
    @0
    ci
    cA
    cmul
    co
    #
    cc
    wcel
    #
    c4
    cn0
    wcel
    #
    @1
    cc
    wcel
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @11
    ax-icn
    @0
    cA
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @0
    @15
    @16
    @17
    w3a
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    #
    simp1bi
    #
    recnd
    #
    ci
    cA
    mulcl
    sylancr
    #
    4nn0
    @10
    vk
    vn
    cF
    c4
    ef01bnd.1
    eftlcl
    sylancl
    abscld
    @0
    @3
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    @0
    @15
    @12
    @22
    @19
    4nn0
    cA
    c4
    reexpcl
    sylancl
    #
    @4
    cr
    wcel
    @6
    cn
    wcel
    @23
    c4
    c1
    4re
    1re
    readdcli
    @5
    c4
    @12
    @5
    cn
    wcel
    4nn0
    c4
    faccl
    ax-mp
    4nn
    nnmulcli
    @4
    @6
    nndivre
    mp2an
    #
    @3
    @7
    remulcl
    sylancl
    @0
    @22
    c6
    cn
    wcel
    @9
    cr
    wcel
    @24
    6nn
    @3
    c6
    nndivre
    sylancl
    @0
    @2
    @10
    cabs
    cfv
    #
    c4
    cexp
    co
    #
    @7
    cmul
    co
    @8
    cle
    @0
    @10
    vk
    vn
    cF
    vn
    cn0
    @26
    vn
    cv
    #
    cexp
    co
    @28
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    vn
    cn0
    @27
    @5
    cdiv
    co
    c1
    @4
    cdiv
    co
    @28
    cexp
    co
    cmul
    co
    cmpt
    #
    c4
    ef01bnd.1
    @29
    eqid
    @30
    eqid
    c4
    cn
    wcel
    @0
    4nn
    a1i
    @21
    @0
    @26
    cA
    c1
    cle
    @0
    @26
    ci
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    cA
    @0
    @13
    @14
    @26
    @33
    wceq
    ax-icn
    @20
    ci
    cA
    absmul
    sylancr
    @0
    @33
    c1
    @32
    cmul
    co
    @34
    @31
    c1
    @32
    cmul
    absi
    oveq1i
    @0
    @32
    cA
    c1
    cmul
    @0
    cA
    crp
    wcel
    #
    @32
    cA
    wceq
    @0
    cA
    @19
    @0
    @15
    @16
    @17
    @18
    simp2bi
    elrpd
    #
    @35
    cA
    cA
    rpre
    cA
    rpge0
    absidd
    syl
    oveq2d
    syl5eq
    @0
    cA
    @20
    mulid2d
    3eqtrd
    #
    @0
    @15
    @16
    @17
    @18
    simp3bi
    eqbrtrd
    eftlub
    @0
    @27
    @3
    @7
    cmul
    @0
    @26
    cA
    c4
    cexp
    @37
    oveq1d
    oveq1d
    breqtrd
    @0
    @8
    @3
    c1
    c6
    cdiv
    co
    #
    cmul
    co
    #
    @9
    clt
    @0
    @7
    @38
    clt
    wbr
    #
    @8
    @39
    clt
    wbr
    #
    c5
    c6
    c2
    c4
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    @42
    @43
    cdiv
    co
    #
    @7
    @38
    clt
    c5
    @42
    clt
    wbr
    #
    @44
    @45
    clt
    wbr
    c5
    c2
    c3
    cexp
    co
    #
    clt
    wbr
    @47
    @42
    cle
    wbr
    #
    @46
    cc0
    c5
    caddc
    co
    #
    c3
    c5
    caddc
    co
    #
    c5
    @47
    clt
    cc0
    c3
    clt
    wbr
    @49
    @50
    clt
    wbr
    3pos
    cc0
    c3
    c5
    0re
    3re
    5re
    ltadd1i
    mpbi
    c5
    5cn
    addid2i
    @47
    c8
    c5
    c3
    caddc
    co
    @50
    cu2
    5p3e8
    c5
    c3
    5cn
    c3
    3nn
    nncni
    addcomi
    3eqtr2ri
    3brtr3i
    c2
    cr
    wcel
    c1
    c2
    cle
    wbr
    c4
    c3
    cuz
    cfv
    wcel
    #
    @48
    2re
    1le2
    @51
    c4
    cz
    wcel
    #
    c3
    c4
    cle
    wbr
    4z
    c3
    c4
    3re
    4re
    3lt4
    ltleii
    c3
    c4
    c3
    3nn
    nnzi
    eluz1i
    mpbir2an
    c2
    c3
    c4
    leexp2a
    mp3an
    c5
    @47
    @42
    5re
    @47
    c8
    cr
    cu2
    8re
    eqeltri
    @42
    c2
    cn
    wcel
    @12
    @42
    cn
    wcel
    2nn
    4nn0
    c2
    c4
    nnexpcl
    mp2an
    #
    nnrei
    #
    ltletri
    mp2an
    c5
    @42
    @43
    5re
    @54
    c6
    @42
    6re
    @54
    remulcli
    c6
    @42
    6re
    @54
    6pos
    @42
    @53
    nngt0i
    mulgt0ii
    ltdiv1ii
    mpbi
    c5
    @4
    @43
    @6
    cdiv
    df-5
    @6
    c3
    cfa
    cfv
    #
    c2
    c2
    cexp
    co
    #
    @56
    cmul
    co
    #
    cmul
    co
    #
    @55
    @42
    cmul
    co
    @43
    @5
    @56
    cmul
    co
    @55
    @56
    cmul
    co
    #
    @56
    cmul
    co
    @6
    @58
    @5
    @59
    @56
    cmul
    @5
    c3
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @55
    @60
    cmul
    co
    #
    @59
    c4
    @60
    cfa
    df-4
    fveq2i
    c3
    cn0
    wcel
    @61
    @62
    wceq
    3nn0
    c3
    facp1
    ax-mp
    @60
    @56
    @55
    cmul
    @56
    c4
    @60
    sq2
    df-4
    eqtr2i
    oveq2i
    3eqtri
    oveq1i
    @56
    c4
    @5
    cmul
    sq2
    oveq2i
    @55
    @56
    @56
    @55
    c6
    cc
    fac3
    6cn
    eqeltri
    @56
    c4
    cc
    sq2
    c4
    4re
    recni
    eqeltri
    #
    @63
    mulassi
    3eqtr3i
    @42
    @57
    @55
    cmul
    c2
    c2
    c2
    caddc
    co
    #
    cexp
    co
    #
    @42
    @57
    @64
    c4
    c2
    cexp
    2p2e4
    oveq2i
    c2
    cc
    wcel
    c2
    cn0
    wcel
    #
    @66
    @65
    @57
    wceq
    2cn
    2nn0
    2nn0
    c2
    c2
    c2
    expadd
    mp3an
    eqtr3i
    oveq2i
    @55
    c6
    @42
    cmul
    fac3
    oveq1i
    3eqtr2ri
    oveq12i
    c1
    @42
    cmul
    co
    #
    @43
    cdiv
    co
    #
    @45
    @38
    @67
    @42
    @43
    cdiv
    @42
    @42
    @53
    nncni
    #
    mulid2i
    oveq1i
    @38
    @42
    @42
    cdiv
    co
    #
    cmul
    co
    @38
    c1
    cmul
    co
    @68
    @38
    @70
    c1
    @38
    cmul
    @42
    @69
    @42
    @53
    nnne0i
    #
    dividi
    oveq2i
    c1
    c6
    @42
    @42
    ax-1cn
    6cn
    @69
    @69
    c6
    6re
    6pos
    gt0ne0ii
    #
    @71
    divmuldivi
    @38
    @38
    c6
    6re
    @72
    rereccli
    #
    recni
    mulid1i
    3eqtr3i
    eqtr3i
    3brtr3i
    @0
    @3
    crp
    wcel
    #
    @40
    @41
    wb
    #
    @0
    @35
    @52
    @74
    @36
    4z
    cA
    c4
    rpexpcl
    sylancl
    @74
    @22
    cc0
    @3
    clt
    wbr
    wa
    #
    @75
    @3
    elrp
    @23
    @38
    cr
    wcel
    @76
    @75
    @25
    @73
    @7
    @38
    @3
    ltmul2
    mp3an12
    sylbi
    syl
    mpbii
    @0
    @3
    cc
    wcel
    #
    @9
    @39
    wceq
    #
    @0
    @3
    @24
    recnd
    @77
    c6
    cc
    wcel
    c6
    cc0
    wne
    @78
    6cn
    @72
    @3
    c6
    divrec
    mp3an23
    syl
    breqtrrd
    lelttrd
end
