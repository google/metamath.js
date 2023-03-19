include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cn0.mm"
include "cneg.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmpt.mm"
include "catan.mm"
include "cli.mm"
include "wceq.mm"
include "2nn0.mm"
include "simpr.mm"
include "nn0mulcl.mm"
include "sylancr.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "nn0cn.mm"
include "adantl.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan3d.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "seqeq3d.mm"
include "cn.mm"
include "cdvds.mm"
include "cif.mm"
include "eqid.mm"
include "atantayl2.mm"
include "neg1cn.mm"
include "expcl.mm"
include "simpll.mm"
include "peano2nn0.mm"
include "syl.mm"
include "expcld.mm"
include "nn0p1nn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "iserodd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem atantayl3
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  assume atantayl3.1: |- F = ( n e. NN0 |-> ( ( -u 1 ^ n ) x. ( ( A ^ ( ( 2 x. n ) + 1 ) ) / ( ( 2 x. n ) + 1 ) ) ) )

  disjoint A n
  disjoint k n
  disjoint A k
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> seq 0 ( + , F ) ~~> ( arctan ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    c1
    clt
    wbr
    #
    wa
    #
    caddc
    cF
    cc0
    cseq
    caddc
    vn
    cn0
    c1
    cneg
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cA
    @6
    cexp
    co
    #
    @6
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    cA
    catan
    cfv
    #
    cli
    @2
    cF
    @13
    caddc
    cc0
    @2
    cF
    vn
    cn0
    @3
    @4
    cexp
    co
    #
    @11
    cmul
    co
    #
    cmpt
    @13
    atantayl3.1
    @2
    vn
    cn0
    @17
    @12
    @2
    @4
    cn0
    wcel
    #
    wa
    #
    @16
    @9
    @11
    cmul
    @19
    @4
    @8
    @3
    cexp
    @19
    @8
    @5
    c2
    cdiv
    co
    @4
    @19
    @7
    @5
    c2
    cdiv
    @19
    @5
    cc
    wcel
    c1
    cc
    wcel
    @7
    @5
    wceq
    @19
    @5
    @19
    c2
    cn0
    wcel
    @18
    @5
    cn0
    wcel
    #
    2nn0
    @2
    @18
    simpr
    #
    c2
    @4
    nn0mulcl
    sylancr
    #
    nn0cnd
    ax-1cn
    @5
    c1
    pncan
    sylancl
    oveq1d
    @19
    @4
    c2
    @18
    @4
    cc
    wcel
    @2
    @4
    nn0cn
    adantl
    @19
    2cnd
    c2
    cc0
    wne
    @19
    2ne0
    a1i
    divcan3d
    eqtr2d
    oveq2d
    oveq1d
    #
    mpteq2dva
    syl5eq
    seqeq3d
    @2
    @14
    @15
    cli
    wbr
    caddc
    vk
    cn
    c2
    vk
    cv
    #
    cdvds
    wbr
    cc0
    @3
    @24
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cA
    @24
    cexp
    co
    #
    @24
    cdiv
    co
    #
    cmul
    co
    #
    cif
    cmpt
    #
    c1
    cseq
    @15
    cli
    wbr
    cA
    vk
    @31
    @31
    eqid
    atantayl2
    @2
    @15
    @30
    @12
    vn
    vk
    @19
    @17
    @12
    cc
    @23
    @19
    @16
    @11
    @19
    @3
    cc
    wcel
    @18
    @16
    cc
    wcel
    neg1cn
    @21
    @3
    @4
    expcl
    sylancr
    @19
    @10
    @6
    @19
    cA
    @6
    @0
    @1
    @18
    simpll
    @19
    @20
    @6
    cn0
    wcel
    @22
    @5
    peano2nn0
    syl
    expcld
    @19
    @6
    @19
    @20
    @6
    cn
    wcel
    @22
    @5
    nn0p1nn
    syl
    #
    nncnd
    @19
    @6
    @32
    nnne0d
    divcld
    mulcld
    eqeltrrd
    @24
    @6
    wceq
    #
    @27
    @9
    @29
    @11
    cmul
    @33
    @26
    @8
    @3
    cexp
    @33
    @25
    @7
    c2
    cdiv
    @24
    @6
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    @33
    @28
    @10
    @24
    @6
    cdiv
    @24
    @6
    cA
    cexp
    oveq2
    @33
    id
    oveq12d
    oveq12d
    iserodd
    mpbird
    eqbrtrd
end
