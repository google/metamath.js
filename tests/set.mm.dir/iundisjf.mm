include "cn.mm"
include "ciun.mm"
include "c1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "cdif.mm"
include "wcel.mm"
include "wrex.mm"
include "csb.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "rabn0.mm"
include "biimpri.mm"
include "infssuzcl.mm"
include "sylancr.mm"
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
include "simpld.mm"
include "simprd.mm"
include "wbr.mm"
include "nnred.mm"
include "ltnrd.mm"
include "eliun.mm"
include "nfrex.mm"
include "nfrab.mm"
include "nfbr.mm"
include "ad2antrr.mm"
include "elfzouz.mm"
include "syl6eleqr.mm"
include "ad2antlr.mm"
include "cle.mm"
include "simpr.mm"
include "sylanbrc.mm"
include "infssuzle.mm"
include "elfzolt2.mm"
include "lelttrd.mm"
include "exp31.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "mtod.mm"
include "eldifd.mm"
include "csbeq1.mm"
include "nfeq2.mm"
include "nfov.mm"
include "oveq2.mm"
include "eqidd.mm"
include "iuneq12df.mm"
include "difeq12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfiun.mm"
include "nfdif.mm"
include "iuneq1d.mm"
include "cbvrex.mm"
include "sylibr.mm"
include "eldifi.mm"
include "reximi.mm"
include "impbii.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iundisjf
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume iundisjf.1: |- F/_ k A
  assume iundisjf.2: |- F/_ n B
  assume iundisjf.3: |- ( n = k -> A = B )

  disjoint k n
  disjoint a b
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A a
  disjoint A b
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B x
  disjoint B y
  assert |- U_ n e. NN A = U_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B )

  proof
    vx
    vn
    cn
    cA
    ciun
    #
    vn
    cn
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
    cn
    wrex
    #
    @6
    @4
    wcel
    #
    vn
    cn
    wrex
    #
    @6
    @0
    wcel
    @6
    @5
    wcel
    @8
    @10
    @8
    @6
    vn
    vm
    cv
    #
    cA
    csb
    #
    vk
    c1
    @11
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
    cn
    wrex
    #
    @10
    @8
    @7
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cn
    wcel
    #
    @6
    vn
    @19
    cA
    csb
    #
    vk
    c1
    @19
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
    @17
    @8
    @20
    @6
    @21
    wcel
    #
    @8
    @19
    @18
    wcel
    #
    @20
    @26
    wa
    @8
    @18
    c1
    cuz
    cfv
    #
    wss
    #
    @18
    c0
    wne
    #
    @27
    @18
    cn
    @28
    @7
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    #
    @30
    @8
    @7
    vn
    cn
    rabn0
    biimpri
    @18
    c1
    infssuzcl
    sylancr
    @7
    @26
    vn
    @19
    cn
    vn
    @18
    cr
    clt
    @7
    vn
    cn
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
    cn
    nfcv
    #
    vn
    vx
    @21
    vn
    @19
    cA
    @32
    nfcsb1
    nfcri
    @1
    @19
    wceq
    cA
    @21
    @6
    vn
    @19
    cA
    csbeq1a
    eleq2d
    elrabf
    sylib
    #
    simpld
    #
    @8
    @6
    @21
    @23
    @8
    @20
    @26
    @34
    simprd
    @8
    @6
    @23
    wcel
    #
    @19
    @19
    clt
    wbr
    #
    @8
    @19
    @8
    @19
    @35
    nnred
    #
    ltnrd
    @36
    @6
    cB
    wcel
    #
    vk
    @22
    wrex
    @8
    @37
    vk
    @6
    @22
    cB
    eliun
    @8
    @39
    @37
    vk
    @22
    @7
    vk
    vn
    cn
    vk
    cn
    nfcv
    #
    vk
    vx
    cA
    iundisjf.1
    nfcri
    #
    nfrex
    vk
    @19
    @19
    clt
    vk
    @18
    cr
    clt
    @7
    vk
    vn
    cn
    @41
    @40
    nfrab
    vk
    cr
    nfcv
    vk
    clt
    nfcv
    #
    nfinf
    #
    @42
    @43
    nfbr
    @8
    vk
    cv
    #
    @22
    wcel
    #
    @39
    @37
    @8
    @45
    wa
    #
    @39
    wa
    #
    @19
    @44
    @19
    @8
    @19
    cr
    wcel
    @45
    @39
    @38
    ad2antrr
    #
    @47
    @44
    @45
    @44
    cn
    wcel
    #
    @8
    @39
    @45
    @44
    @28
    cn
    @44
    c1
    @19
    elfzouz
    nnuz
    syl6eleqr
    ad2antlr
    #
    nnred
    @48
    @47
    @29
    @44
    @18
    wcel
    #
    @19
    @44
    cle
    wbr
    @31
    @47
    @49
    @39
    @51
    @50
    @46
    @39
    simpr
    @7
    @39
    vn
    @44
    cn
    vn
    @44
    nfcv
    @33
    vn
    vx
    cB
    iundisjf.2
    nfcri
    @1
    @44
    wceq
    cA
    cB
    @6
    iundisjf.3
    eleq2d
    elrabf
    sylanbrc
    @44
    @18
    c1
    infssuzle
    sylancr
    @45
    @44
    @19
    clt
    wbr
    @8
    @39
    @44
    c1
    @19
    elfzolt2
    ad2antlr
    lelttrd
    exp31
    rexlimd
    syl5bi
    mtod
    eldifd
    @16
    @25
    vm
    @19
    cn
    @11
    @19
    wceq
    #
    @15
    @24
    @6
    @52
    @12
    @21
    @14
    @23
    vn
    @11
    @19
    cA
    csbeq1
    @52
    vk
    @13
    @22
    cB
    cB
    vk
    @11
    @19
    @43
    nfeq2
    vk
    @13
    nfcv
    vk
    c1
    @19
    cfzo
    vk
    c1
    nfcv
    vk
    cfzo
    nfcv
    @43
    nfov
    @11
    @19
    c1
    cfzo
    oveq2
    @52
    cB
    eqidd
    iuneq12df
    difeq12d
    eleq2d
    rspcev
    syl2anc
    @9
    @16
    vn
    vm
    cn
    @9
    vm
    nfv
    vn
    vx
    @15
    vn
    @12
    @14
    vn
    @11
    cA
    nfcsb1v
    vk
    vn
    @13
    cB
    vn
    @13
    nfcv
    iundisjf.2
    nfiun
    nfdif
    nfcri
    @1
    @11
    wceq
    #
    @4
    @15
    @6
    @53
    cA
    @12
    @3
    @14
    vn
    @11
    cA
    csbeq1a
    @53
    vk
    @2
    @13
    cB
    @1
    @11
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    eleq2d
    cbvrex
    sylibr
    @9
    @7
    vn
    cn
    @6
    cA
    @3
    eldifi
    reximi
    impbii
    vn
    @6
    cn
    cA
    eliun
    vn
    @6
    cn
    @4
    eliun
    3bitr4i
    eqriv
end
