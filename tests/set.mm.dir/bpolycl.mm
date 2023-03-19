include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cbp.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "r19.21v.mm"
include "w3a.mm"
include "cexp.mm"
include "cbc.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "bpolyval.mm"
include "3adant3.mm"
include "simp2.mm"
include "simp1.mm"
include "expcld.mm"
include "fzfid.mm"
include "wa.mm"
include "cz.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "rspccva.mm"
include "3ad2antl3.mm"
include "cn.mm"
include "fzssp1.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "fznn0sub.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "a2d.mm"
include "syl5bi.mm"
include "nn0sinds.mm"
include "imp.mm"

theorem bpolycl
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m


  assert |- ( ( N e. NN0 /\ X e. CC ) -> ( N BernPoly X ) e. CC )

  proof
    cN
    cn0
    wcel
    cX
    cc
    wcel
    #
    cN
    cX
    cbp
    co
    #
    cc
    wcel
    #
    @0
    vn
    cv
    #
    cX
    cbp
    co
    #
    cc
    wcel
    #
    wi
    #
    @0
    vk
    cv
    #
    cX
    cbp
    co
    #
    cc
    wcel
    #
    wi
    #
    @0
    @2
    wi
    vn
    vk
    cN
    @3
    @7
    wceq
    #
    @5
    @9
    @0
    @11
    @4
    @8
    cc
    @3
    @7
    cX
    cbp
    oveq1
    eleq1d
    imbi2d
    @3
    cN
    wceq
    #
    @5
    @2
    @0
    @12
    @4
    @1
    cc
    @3
    cN
    cX
    cbp
    oveq1
    eleq1d
    imbi2d
    @10
    vk
    cc0
    @3
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    @0
    @9
    vk
    @14
    wral
    #
    wi
    @3
    cn0
    wcel
    #
    @6
    @0
    @9
    vk
    @14
    r19.21v
    @16
    @0
    @15
    @5
    @16
    @0
    @15
    @5
    @16
    @0
    @15
    w3a
    #
    @4
    cX
    @3
    cexp
    co
    #
    @14
    @3
    vm
    cv
    #
    cbc
    co
    #
    @19
    cX
    cbp
    co
    #
    @3
    @19
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmin
    co
    #
    cc
    @16
    @0
    @4
    @27
    wceq
    @15
    vm
    @3
    cX
    bpolyval
    3adant3
    @17
    @18
    @26
    @17
    cX
    @3
    @16
    @0
    @15
    simp2
    @16
    @0
    @15
    simp1
    #
    expcld
    @17
    @14
    @25
    vm
    @17
    cc0
    @13
    fzfid
    @17
    @19
    @14
    wcel
    #
    wa
    #
    @20
    @24
    @30
    @20
    @17
    @16
    @19
    cz
    wcel
    @20
    cn0
    wcel
    @29
    @28
    @19
    cc0
    @13
    elfzelz
    @19
    @3
    bccl
    syl2an
    nn0cnd
    @30
    @21
    @23
    @15
    @16
    @29
    @21
    cc
    wcel
    #
    @0
    @9
    @31
    vk
    @19
    @14
    @7
    @19
    wceq
    @8
    @21
    cc
    @7
    @19
    cX
    cbp
    oveq1
    eleq1d
    rspccva
    3ad2antl3
    @30
    @23
    @30
    @19
    cc0
    @3
    cfz
    co
    #
    wcel
    @22
    cn0
    wcel
    @23
    cn
    wcel
    @17
    @14
    @32
    @19
    @17
    cc0
    @13
    c1
    caddc
    co
    #
    cfz
    co
    @14
    @32
    cc0
    @13
    fzssp1
    @17
    @33
    @3
    cc0
    cfz
    @17
    @3
    cc
    wcel
    c1
    cc
    wcel
    @33
    @3
    wceq
    @17
    @3
    @28
    nn0cnd
    ax-1cn
    @3
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    sselda
    @19
    cc0
    @3
    fznn0sub
    @22
    nn0p1nn
    3syl
    #
    nncnd
    @30
    @23
    @34
    nnne0d
    divcld
    mulcld
    fsumcl
    subcld
    eqeltrd
    3exp
    a2d
    syl5bi
    nn0sinds
    imp
end
