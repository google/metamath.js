include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wrex.mm"
include "csb.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ssrab2.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cn.mm"
include "fzossnn.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "sstri.mm"
include "rabn0.mm"
include "biimpri.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "wa.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfinf.mm"
include "nfcsb1.mm"
include "nfcri.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq2d.mm"
include "elrabf.mm"
include "sylib.mm"
include "simprd.mm"
include "wbr.mm"
include "nnssre.mm"
include "ltnrd.mm"
include "eliun.mm"
include "ad2antrr.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "3syl.mm"
include "sselda.mm"
include "adantr.mm"
include "nnred.mm"
include "cle.mm"
include "simpr.mm"
include "sylanbrc.mm"
include "infssuzle.mm"
include "elfzolt2.mm"
include "ad2antlr.mm"
include "lelttrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "mtod.mm"
include "eldifd.mm"
include "csbeq1.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfiun.mm"
include "nfdif.mm"
include "cbvrex.mm"
include "sylibr.mm"
include "eldifi.mm"
include "reximi.mm"
include "impbii.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iundisjfi
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  assume iundisj3.0: |- F/_ n B
  assume iundisj3.1: |- ( n = k -> A = B )

  disjoint k n
  disjoint N k
  disjoint N n
  disjoint A k
  disjoint k m
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint N m
  disjoint n x
  disjoint N x
  disjoint A m
  disjoint A x
  disjoint B m
  disjoint B x
  assert |- U_ n e. ( 1 ..^ N ) A = U_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B )

  proof
    vx
    vn
    c1
    cN
    cfzo
    co
    #
    cA
    ciun
    #
    vn
    @0
    cA
    vk
    c1
    vn
    cv
    #
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    ciun
    #
    vx
    cv
    #
    cA
    wcel
    #
    vn
    @0
    wrex
    #
    @7
    @5
    wcel
    #
    vn
    @0
    wrex
    #
    @7
    @1
    wcel
    @7
    @6
    wcel
    @9
    @11
    @9
    @7
    vn
    vm
    cv
    #
    cA
    csb
    #
    vk
    c1
    @12
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    wcel
    #
    vm
    @0
    wrex
    #
    @11
    @9
    @8
    vn
    @0
    crab
    #
    cr
    clt
    cinf
    #
    @0
    wcel
    #
    @7
    vn
    @20
    cA
    csb
    #
    vk
    c1
    @20
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    wcel
    #
    @18
    @9
    @19
    @0
    @20
    @8
    vn
    @0
    ssrab2
    #
    @9
    @19
    c1
    cuz
    cfv
    #
    wss
    #
    @19
    c0
    wne
    #
    @20
    @19
    wcel
    #
    @19
    @0
    @28
    @27
    @0
    cn
    @28
    cN
    fzossnn
    #
    nnuz
    sseqtri
    sstri
    #
    @30
    @9
    @8
    vn
    @0
    rabn0
    biimpri
    @19
    c1
    infssuzcl
    sylancr
    #
    sseldi
    #
    @9
    @7
    @22
    @24
    @9
    @21
    @7
    @22
    wcel
    #
    @9
    @31
    @21
    @36
    wa
    @34
    @8
    @36
    vn
    @20
    @0
    vn
    @19
    cr
    clt
    @8
    vn
    @0
    nfrab1
    vn
    cr
    nfcv
    vn
    clt
    nfcv
    nfinf
    #
    vn
    @0
    nfcv
    #
    vn
    vx
    @22
    vn
    @20
    cA
    @37
    nfcsb1
    nfcri
    @2
    @20
    wceq
    cA
    @22
    @7
    vn
    @20
    cA
    csbeq1a
    eleq2d
    elrabf
    sylib
    simprd
    @9
    @7
    @24
    wcel
    #
    @20
    @20
    clt
    wbr
    #
    @9
    @20
    @9
    @19
    cr
    @20
    @19
    cn
    cr
    @19
    @0
    cn
    @27
    @32
    sstri
    nnssre
    sstri
    @34
    sseldi
    #
    ltnrd
    @39
    @7
    cB
    wcel
    #
    vk
    @23
    wrex
    @9
    @40
    vk
    @7
    @23
    cB
    eliun
    @9
    @42
    @40
    vk
    @23
    @9
    vk
    cv
    #
    @23
    wcel
    #
    wa
    #
    @42
    @40
    @45
    @42
    wa
    #
    @20
    @43
    @20
    @9
    @20
    cr
    wcel
    @44
    @42
    @41
    ad2antrr
    #
    @46
    @43
    @46
    @0
    cn
    @43
    @32
    @45
    @43
    @0
    wcel
    #
    @42
    @9
    @23
    @0
    @43
    @9
    @21
    cN
    @20
    cuz
    cfv
    wcel
    @23
    @0
    wss
    @35
    @20
    c1
    cN
    elfzouz2
    @20
    c1
    cN
    fzoss2
    3syl
    sselda
    adantr
    #
    sseldi
    nnred
    @47
    @46
    @29
    @43
    @19
    wcel
    #
    @20
    @43
    cle
    wbr
    @33
    @46
    @48
    @42
    @50
    @49
    @45
    @42
    simpr
    @8
    @42
    vn
    @43
    @0
    vn
    @43
    nfcv
    @38
    vn
    vx
    cB
    iundisj3.0
    nfcri
    @2
    @43
    wceq
    cA
    cB
    @7
    iundisj3.1
    eleq2d
    elrabf
    sylanbrc
    @43
    @19
    c1
    infssuzle
    sylancr
    @44
    @43
    @20
    clt
    wbr
    @9
    @42
    @43
    c1
    @20
    elfzolt2
    ad2antlr
    lelttrd
    ex
    rexlimdva
    syl5bi
    mtod
    eldifd
    @17
    @26
    vm
    @20
    @0
    @12
    @20
    wceq
    #
    @16
    @25
    @7
    @51
    @13
    @22
    @15
    @24
    vn
    @12
    @20
    cA
    csbeq1
    @51
    vk
    @14
    @23
    cB
    @12
    @20
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    eleq2d
    rspcev
    syl2anc
    @10
    @17
    vn
    vm
    @0
    @10
    vm
    nfv
    vn
    vx
    @16
    vn
    @13
    @15
    vn
    @12
    cA
    nfcsb1v
    vk
    vn
    @14
    cB
    vn
    @14
    nfcv
    iundisj3.0
    nfiun
    nfdif
    nfcri
    @2
    @12
    wceq
    #
    @5
    @16
    @7
    @52
    cA
    @13
    @4
    @15
    vn
    @12
    cA
    csbeq1a
    @52
    vk
    @3
    @14
    cB
    @2
    @12
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    eleq2d
    cbvrex
    sylibr
    @10
    @8
    vn
    @0
    @7
    cA
    @4
    eldifi
    reximi
    impbii
    vn
    @7
    @0
    cA
    eliun
    vn
    @7
    @0
    @5
    eliun
    3bitr4i
    eqriv
end
