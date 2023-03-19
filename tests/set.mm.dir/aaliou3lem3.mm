include "cn.mm"
include "wcel.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "crp.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "syl.mm"
include "aaliou3lem1.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "cioc.mm"
include "w3a.mm"
include "aaliou3lem2.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "cc.mm"
include "halfcn.mm"
include "a1i.mm"
include "cabs.mm"
include "wceq.mm"
include "halfre.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "rprege0.mm"
include "absid.mm"
include "mp2b.mm"
include "halflt1.mm"
include "eqbrtri.mm"
include "2rp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "nnzd.mm"
include "znegcld.mm"
include "rpexpcl.mm"
include "rpcnd.mm"
include "geolim3.mm"
include "seqex.mm"
include "ovex.mm"
include "breldm.mm"
include "simp2d.mm"
include "elrpd.mm"
include "rpge0d.mm"
include "simp3d.mm"
include "cvgcmp.mm"
include "eqidd.mm"
include "isumrpcl.mm"
include "isumle.mm"
include "recnd.mm"
include "isumclim.mm"
include "1mhlfehlf.mm"
include "oveq2i.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancl.mm"
include "div1d.mm"
include "wne.mm"
include "1rp.mm"
include "rpcnne0.mm"
include "ax-mp.mm"
include "2cnne0.mm"
include "divdiv2.mm"
include "mp3an23.mm"
include "mulcom.mm"
include "3eqtr4d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "3jca.mm"

theorem aaliou3lem3
  let cA: class A
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
  assume aaliou3lem.a: |- G = ( c e. ( ZZ>= ` A ) |-> ( ( 2 ^ -u ( ! ` A ) ) x. ( ( 1 / 2 ) ^ ( c - A ) ) ) )
  assume aaliou3lem.b: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )

  disjoint F b
  disjoint F c
  disjoint b c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint G a
  disjoint G b
  disjoint F d
  disjoint b d
  disjoint c d
  disjoint A d
  disjoint a d
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint G d
  assert |- ( A e. NN -> ( seq A ( + , F ) e. dom ~~> /\ sum_ b e. ( ZZ>= ` A ) ( F ` b ) e. RR+ /\ sum_ b e. ( ZZ>= ` A ) ( F ` b ) <_ ( 2 x. ( 2 ^ -u ( ! ` A ) ) ) ) )

  proof
    cA
    cn
    wcel
    #
    caddc
    cF
    cA
    cseq
    cli
    cdm
    #
    wcel
    cA
    cuz
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    vb
    csu
    #
    crp
    wcel
    @5
    c2
    c2
    cA
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    @0
    vb
    cG
    cF
    cA
    cA
    @2
    @2
    eqid
    #
    @0
    cA
    cz
    wcel
    cA
    @2
    wcel
    cA
    nnz
    #
    cA
    uzid
    syl
    #
    cA
    @3
    cG
    vc
    aaliou3lem.a
    aaliou3lem1
    #
    @0
    @3
    @2
    wcel
    wa
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @4
    @3
    cG
    cfv
    #
    cle
    wbr
    #
    @14
    @4
    cc0
    @17
    cioc
    co
    wcel
    #
    @15
    @16
    @18
    w3a
    #
    cA
    @3
    cF
    cG
    va
    vc
    aaliou3lem.a
    aaliou3lem.b
    aaliou3lem2
    @14
    cc0
    cxr
    wcel
    @17
    cr
    wcel
    @19
    @20
    wb
    0xr
    @13
    cc0
    @17
    @4
    elioc2
    sylancr
    mpbid
    #
    simp1d
    #
    @0
    caddc
    cG
    cA
    cseq
    #
    @8
    c1
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    @23
    @1
    wcel
    @0
    cA
    @24
    @8
    vc
    cG
    @11
    @24
    cc
    wcel
    @0
    halfcn
    a1i
    @24
    cabs
    cfv
    #
    c1
    clt
    wbr
    @0
    @27
    @24
    c1
    clt
    @24
    crp
    wcel
    @24
    cr
    wcel
    cc0
    @24
    cle
    wbr
    wa
    @27
    @24
    wceq
    @24
    halfre
    halfgt0
    elrpii
    @24
    rprege0
    @24
    absid
    mp2b
    halflt1
    eqbrtri
    a1i
    @0
    @8
    @0
    c2
    crp
    wcel
    @7
    cz
    wcel
    @8
    crp
    wcel
    2rp
    @0
    @6
    @0
    @6
    @0
    cA
    cn0
    wcel
    @6
    cn
    wcel
    cA
    nnnn0
    cA
    faccl
    syl
    nnzd
    znegcld
    c2
    @7
    rpexpcl
    sylancr
    rpcnd
    #
    aaliou3lem.a
    geolim3
    #
    @23
    @26
    cli
    caddc
    cG
    cA
    seqex
    @8
    @25
    cdiv
    ovex
    breldm
    syl
    #
    @14
    @4
    @14
    @4
    @22
    @14
    @15
    @16
    @18
    @21
    simp2d
    elrpd
    #
    rpge0d
    @14
    @15
    @16
    @18
    @21
    simp3d
    #
    cvgcmp
    #
    @0
    @4
    vb
    cF
    cA
    cA
    @2
    @2
    @10
    @10
    @12
    @14
    @4
    eqidd
    #
    @31
    @33
    isumrpcl
    @0
    @5
    @2
    @17
    vb
    csu
    #
    @9
    cle
    @0
    @4
    @17
    vb
    cF
    cG
    cA
    @2
    @10
    @11
    @34
    @22
    @14
    @17
    eqidd
    #
    @13
    @32
    @33
    @30
    isumle
    @0
    @35
    @26
    @9
    @0
    @17
    @26
    vb
    cG
    cA
    @2
    @10
    @11
    @36
    @14
    @17
    @13
    recnd
    @29
    isumclim
    @0
    @26
    @8
    @24
    cdiv
    co
    #
    @9
    @25
    @24
    @8
    cdiv
    1mhlfehlf
    oveq2i
    @0
    @8
    c2
    cmul
    co
    #
    c1
    cdiv
    co
    #
    @38
    @37
    @9
    @0
    @38
    @0
    @8
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    @38
    cc
    wcel
    @28
    2cn
    @8
    c2
    mulcl
    sylancl
    div1d
    @0
    @40
    @37
    @39
    wceq
    #
    @28
    @40
    c1
    cc
    wcel
    c1
    cc0
    wne
    wa
    #
    @41
    c2
    cc0
    wne
    wa
    @42
    c1
    crp
    wcel
    @43
    1rp
    c1
    rpcnne0
    ax-mp
    2cnne0
    @8
    c1
    c2
    divdiv2
    mp3an23
    syl
    @0
    @41
    @40
    @9
    @38
    wceq
    2cn
    @28
    c2
    @8
    mulcom
    sylancr
    3eqtr4d
    syl5eq
    eqtrd
    breqtrd
    3jca
end
