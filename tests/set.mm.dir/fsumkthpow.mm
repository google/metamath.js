include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "cbp.mm"
include "cmin.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "adantr.mm"
include "nncnd.mm"
include "fzfid.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "simpl.mm"
include "expcl.mm"
include "syl2anr.mm"
include "fsumcl.mm"
include "nnne0d.mm"
include "cmul.mm"
include "fsummulc2.mm"
include "wceq.mm"
include "bpolydif.mm"
include "syl2an.mm"
include "nn0cn.mm"
include "ad2antrr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "oveq2.mm"
include "cz.mm"
include "nn0z.mm"
include "adantl.mm"
include "cuz.mm"
include "cfv.mm"
include "peano2nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "bpolycl.mm"
include "syl2anc.mm"
include "telfsum2.mm"
include "3eqtr2d.mm"
include "mvllmuld.mm"

theorem fsumkthpow
  let vn: setvar n
  let cK: class K
  let cM: class M
  let vk: setvar k

  disjoint K n
  disjoint M n
  disjoint K k
  disjoint k n
  disjoint M k
  assert |- ( ( K e. NN0 /\ M e. NN0 ) -> sum_ n e. ( 0 ... M ) ( n ^ K ) = ( ( ( ( K + 1 ) BernPoly ( M + 1 ) ) - ( ( K + 1 ) BernPoly 0 ) ) / ( K + 1 ) ) )

  proof
    cK
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cK
    c1
    caddc
    co
    #
    cc0
    cM
    cfz
    co
    #
    vn
    cv
    #
    cK
    cexp
    co
    #
    vn
    csu
    #
    @3
    cM
    c1
    caddc
    co
    #
    cbp
    co
    #
    @3
    cc0
    cbp
    co
    #
    cmin
    co
    #
    @2
    @3
    @0
    @3
    cn
    wcel
    #
    @1
    cK
    nn0p1nn
    adantr
    #
    nncnd
    #
    @2
    @4
    @6
    vn
    @2
    cc0
    cM
    fzfid
    #
    @5
    @4
    wcel
    #
    @5
    cc
    wcel
    #
    @0
    @6
    cc
    wcel
    @2
    @16
    @5
    @5
    cc0
    cM
    elfzelz
    zcnd
    #
    @0
    @1
    simpl
    @5
    cK
    expcl
    syl2anr
    #
    fsumcl
    @2
    @3
    @13
    nnne0d
    @2
    @3
    @7
    cmul
    co
    @4
    @3
    @6
    cmul
    co
    #
    vn
    csu
    @4
    @3
    @5
    c1
    caddc
    co
    #
    cbp
    co
    #
    @3
    @5
    cbp
    co
    #
    cmin
    co
    #
    vn
    csu
    @11
    @2
    @4
    @6
    @3
    vn
    @15
    @14
    @19
    fsummulc2
    @2
    @4
    @24
    @20
    vn
    @2
    @16
    wa
    #
    @24
    @3
    @5
    @3
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @20
    @2
    @12
    @17
    @24
    @28
    wceq
    @16
    @13
    @18
    @3
    @5
    bpolydif
    syl2an
    @25
    @27
    @6
    @3
    cmul
    @25
    @26
    cK
    @5
    cexp
    @25
    cK
    cc
    wcel
    #
    c1
    cc
    wcel
    @26
    cK
    wceq
    @0
    @29
    @1
    @16
    cK
    nn0cn
    ad2antrr
    ax-1cn
    cK
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    eqtrd
    sumeq2dv
    @2
    @3
    vk
    cv
    #
    cbp
    co
    #
    @23
    @22
    @10
    vn
    vk
    @9
    cc0
    cM
    @30
    @5
    @3
    cbp
    oveq2
    @30
    @21
    @3
    cbp
    oveq2
    @30
    cc0
    @3
    cbp
    oveq2
    @30
    @8
    @3
    cbp
    oveq2
    @1
    cM
    cz
    wcel
    @0
    cM
    nn0z
    adantl
    @2
    @8
    cn0
    cc0
    cuz
    cfv
    @1
    @8
    cn0
    wcel
    @0
    cM
    peano2nn0
    adantl
    nn0uz
    syl6eleq
    @2
    @30
    cc0
    @8
    cfz
    co
    wcel
    #
    wa
    #
    @3
    cn0
    wcel
    #
    @30
    cc
    wcel
    @31
    cc
    wcel
    @0
    @34
    @1
    @32
    cK
    peano2nn0
    ad2antrr
    @33
    @30
    @32
    @30
    cn0
    wcel
    @2
    @30
    @8
    elfznn0
    adantl
    nn0cnd
    @3
    @30
    bpolycl
    syl2anc
    telfsum2
    3eqtr2d
    mvllmuld
end
