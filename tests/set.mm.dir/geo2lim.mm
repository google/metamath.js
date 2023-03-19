include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cli.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cmul.mm"
include "cn0.mm"
include "c2.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cmpt.mm"
include "halfcn.mm"
include "a1i.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cle.mm"
include "wceq.mm"
include "halfre.mm"
include "0re.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "absid.mm"
include "mp2an.mm"
include "halflt1.mm"
include "eqbrtri.mm"
include "expcnv.mm"
include "id.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "wa.mm"
include "nnnn0.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cz.mm"
include "nnz.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "exprec.mm"
include "mp3an12.mm"
include "eqtrd.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrecred.mm"
include "recnd.mm"
include "eqeltrd.mm"
include "simpl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divrecd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "climmulc2.mm"
include "mul01.mm"
include "breqtrd.mm"
include "seqex.mm"
include "divcld.mm"
include "cfz.mm"
include "csu.mm"
include "geo2sum.mm"
include "ancoms.mm"
include "elfznn.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "simpll.mm"
include "fsumser.mm"
include "3eqtr2rd.mm"
include "climsubc2.mm"
include "subid1.mm"

theorem geo2lim
  let cA: class A
  let vk: setvar k
  let cF: class F
  let vj: setvar j
  let vn: setvar n
  assume geo2lim.1: |- F = ( k e. NN |-> ( A / ( 2 ^ k ) ) )

  disjoint A k
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint k n
  disjoint A n
  disjoint F j
  disjoint F n
  assert |- ( A e. CC -> seq 1 ( + , F ) ~~> A )

  proof
    cA
    cc
    wcel
    #
    caddc
    cF
    c1
    cseq
    #
    cA
    cc0
    cmin
    co
    cA
    cli
    @0
    cc0
    cA
    vj
    cF
    @1
    c1
    cvv
    cn
    nnuz
    @0
    1zzd
    #
    @0
    cF
    cA
    cc0
    cmul
    co
    cc0
    cli
    @0
    cc0
    cA
    vj
    vk
    cn0
    c1
    c2
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cF
    c1
    cvv
    cn
    nnuz
    @2
    @0
    @3
    vk
    @3
    cc
    wcel
    @0
    halfcn
    a1i
    @3
    cabs
    cfv
    #
    c1
    clt
    wbr
    @0
    @7
    @3
    c1
    clt
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    @7
    @3
    wceq
    halfre
    cc0
    @3
    0re
    halfre
    halfgt0
    ltleii
    @3
    absid
    mp2an
    halflt1
    eqbrtri
    a1i
    expcnv
    @0
    id
    #
    cF
    cvv
    wcel
    @0
    cF
    vk
    cn
    cA
    c2
    @4
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    cvv
    geo2lim.1
    vk
    cn
    @10
    nnex
    mptex
    eqeltri
    a1i
    @0
    vj
    cv
    #
    cn
    wcel
    #
    wa
    #
    @11
    @6
    cfv
    #
    c1
    c2
    @11
    cexp
    co
    #
    cdiv
    co
    #
    cc
    @13
    @14
    @3
    @11
    cexp
    co
    #
    @16
    @13
    @11
    cn0
    wcel
    #
    @14
    @17
    wceq
    @12
    @18
    @0
    @11
    nnnn0
    adantl
    #
    vk
    @11
    @5
    @17
    cn0
    @6
    @4
    @11
    @3
    cexp
    oveq2
    @6
    eqid
    @3
    @11
    cexp
    ovex
    fvmpt
    syl
    @13
    @11
    cz
    wcel
    #
    @17
    @16
    wceq
    #
    @12
    @20
    @0
    @11
    nnz
    adantl
    c2
    cc
    wcel
    c2
    cc0
    wne
    @20
    @21
    2cn
    2ne0
    c2
    @11
    exprec
    mp3an12
    syl
    eqtrd
    #
    @13
    @16
    @13
    @15
    @13
    c2
    cn
    wcel
    #
    @18
    @15
    cn
    wcel
    2nn
    @19
    c2
    @11
    nnexpcl
    sylancr
    #
    nnrecred
    recnd
    eqeltrd
    @13
    cA
    @15
    cdiv
    co
    #
    cA
    @16
    cmul
    co
    @11
    cF
    cfv
    #
    cA
    @14
    cmul
    co
    @13
    cA
    @15
    @0
    @12
    simpl
    #
    @13
    @15
    @24
    nncnd
    #
    @13
    @15
    @24
    nnne0d
    #
    divrecd
    @12
    @26
    @25
    wceq
    @0
    vk
    @11
    @10
    @25
    cn
    cF
    @4
    @11
    wceq
    @9
    @15
    cA
    cdiv
    @4
    @11
    c2
    cexp
    oveq2
    oveq2d
    geo2lim.1
    cA
    @15
    cdiv
    ovex
    fvmpt
    adantl
    #
    @13
    @14
    @16
    cA
    cmul
    @22
    oveq2d
    3eqtr4d
    climmulc2
    cA
    mul01
    breqtrd
    @8
    @1
    cvv
    wcel
    @0
    caddc
    cF
    c1
    seqex
    a1i
    @13
    @26
    @25
    cc
    @30
    @13
    cA
    @15
    @27
    @28
    @29
    divcld
    eqeltrd
    @13
    cA
    @26
    cmin
    co
    cA
    @25
    cmin
    co
    #
    c1
    @11
    cfz
    co
    #
    cA
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    vn
    csu
    #
    @11
    @1
    cfv
    @13
    @26
    @25
    cA
    cmin
    @30
    oveq2d
    @12
    @0
    @36
    @31
    wceq
    cA
    vn
    @11
    geo2sum
    ancoms
    @13
    @35
    vn
    cF
    c1
    @11
    @13
    @33
    @32
    wcel
    #
    wa
    #
    @33
    cn
    wcel
    #
    @33
    cF
    cfv
    @35
    wceq
    @37
    @39
    @13
    @33
    @11
    elfznn
    adantl
    #
    vk
    @33
    @10
    @35
    cn
    cF
    @4
    @33
    wceq
    @9
    @34
    cA
    cdiv
    @4
    @33
    c2
    cexp
    oveq2
    oveq2d
    geo2lim.1
    cA
    @34
    cdiv
    ovex
    fvmpt
    syl
    @13
    @11
    cn
    c1
    cuz
    cfv
    @0
    @12
    simpr
    nnuz
    syl6eleq
    @38
    cA
    @34
    @0
    @12
    @37
    simpll
    @38
    @34
    @38
    @39
    @34
    cn
    wcel
    #
    @40
    @39
    @23
    @33
    cn0
    wcel
    @41
    2nn
    @33
    nnnn0
    c2
    @33
    nnexpcl
    sylancr
    syl
    #
    nncnd
    @38
    @34
    @42
    nnne0d
    divcld
    fsumser
    3eqtr2rd
    climsubc2
    cA
    subid1
    breqtrd
end
