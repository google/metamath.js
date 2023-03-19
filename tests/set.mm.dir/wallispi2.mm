include "cn.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "cmpt.mm"
include "eqid.mm"
include "c4.mm"
include "cexp.mm"
include "cseq.mm"
include "cfv.mm"
include "cfa.mm"
include "wcel.mm"
include "1cnd.mm"
include "2cnd.mm"
include "nncn.mm"
include "mulcld.mm"
include "addcld.mm"
include "cc.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "cfz.mm"
include "eqidd.mm"
include "weq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "elfznn.mm"
include "nncnd.mm"
include "cn0.mm"
include "4nn0.mm"
include "a1i.mm"
include "expcld.mm"
include "subcld.mm"
include "sqcld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "nnne0d.mm"
include "mulne0d.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "remulcld.mm"
include "nnred.mm"
include "clt.mm"
include "wbr.mm"
include "1lt2.mm"
include "2t1e2.mm"
include "syl6breqr.mm"
include "cle.mm"
include "0le2.mm"
include "elfzle1.mm"
include "lemul2ad.mm"
include "ltletrd.mm"
include "gtned.mm"
include "subne0d.mm"
include "cz.mm"
include "2z.mm"
include "expne0d.mm"
include "divcld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "mulcl.mm"
include "seqcl.mm"
include "2nn.mm"
include "id.mm"
include "nnmulcld.mm"
include "peano2nnd.mm"
include "div32d.mm"
include "mulid2d.mm"
include "wallispi2lem2.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "wallispi2lem1.mm"
include "3eqtr4ri.mm"
include "wallispi.mm"

theorem wallispi2
  let vn: setvar n
  let cV: class V
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  assume wallispi2.1: |- V = ( n e. NN |-> ( ( ( ( 2 ^ ( 4 x. n ) ) x. ( ( ! ` n ) ^ 4 ) ) / ( ( ! ` ( 2 x. n ) ) ^ 2 ) ) / ( ( 2 x. n ) + 1 ) ) )


  assert |- V ~~> ( _pi / 2 )

  proof
    vk
    vn
    vk
    cn
    c2
    vk
    cv
    #
    cmul
    co
    #
    @1
    c1
    cmin
    co
    #
    cdiv
    co
    @1
    @1
    c1
    caddc
    co
    cdiv
    co
    cmul
    co
    cmpt
    #
    cV
    @3
    eqid
    vn
    cn
    c1
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
    cdiv
    co
    @4
    cmul
    vk
    cn
    @1
    c4
    cexp
    co
    #
    @1
    @2
    cmul
    co
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    cfv
    #
    cmul
    co
    #
    cmpt
    vn
    cn
    c2
    c4
    @4
    cmul
    co
    cexp
    co
    @4
    cfa
    cfv
    c4
    cexp
    co
    cmul
    co
    @5
    cfa
    cfv
    c2
    cexp
    co
    cdiv
    co
    #
    @6
    cdiv
    co
    #
    cmpt
    vn
    cn
    @4
    cmul
    @3
    c1
    cseq
    cfv
    #
    cmpt
    cV
    vn
    cn
    @13
    @15
    @4
    cn
    wcel
    #
    @13
    c1
    @12
    @6
    cdiv
    co
    #
    cmul
    co
    @18
    @15
    @17
    c1
    @6
    @12
    @17
    1cnd
    #
    @17
    @5
    c1
    @17
    c2
    @4
    @17
    2cnd
    @4
    nncn
    mulcld
    @19
    addcld
    #
    @17
    vm
    vw
    cmul
    cc
    @11
    c1
    @4
    @17
    @4
    c1
    cuz
    cfv
    wcel
    @4
    elnnuz
    biimpi
    vm
    cv
    #
    c1
    @4
    cfz
    co
    wcel
    #
    @21
    @11
    cfv
    #
    cc
    wcel
    @17
    @22
    @23
    c2
    @21
    cmul
    co
    #
    c4
    cexp
    co
    #
    @24
    @24
    c1
    cmin
    co
    #
    cmul
    co
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cc
    @22
    vk
    @21
    @10
    @29
    cn
    @11
    cc
    @22
    @11
    eqidd
    @22
    vk
    vm
    weq
    #
    wa
    #
    @7
    @25
    @9
    @28
    cdiv
    @31
    @1
    @24
    c4
    cexp
    @31
    @0
    @21
    c2
    cmul
    @22
    @30
    simpr
    oveq2d
    #
    oveq1d
    @31
    @8
    @27
    c2
    cexp
    @31
    @1
    @24
    @2
    @26
    cmul
    @32
    @31
    @1
    @24
    c1
    cmin
    @32
    oveq1d
    oveq12d
    oveq1d
    oveq12d
    @21
    @4
    elfznn
    #
    @22
    @25
    @28
    @22
    @24
    c4
    @22
    c2
    @21
    @22
    2cnd
    #
    @22
    @21
    @33
    nncnd
    #
    mulcld
    #
    c4
    cn0
    wcel
    @22
    4nn0
    a1i
    expcld
    @22
    @27
    @22
    @24
    @26
    @36
    @22
    @24
    c1
    @36
    @22
    1cnd
    #
    subcld
    #
    mulcld
    #
    sqcld
    @22
    @27
    c2
    @39
    @22
    @24
    @26
    @36
    @38
    @22
    c2
    @21
    @34
    @35
    c2
    cc0
    wne
    @22
    2ne0
    a1i
    @22
    @21
    @33
    nnne0d
    mulne0d
    @22
    @24
    c1
    @36
    @37
    @22
    c1
    @24
    @22
    1red
    #
    @22
    c1
    c2
    c1
    cmul
    co
    #
    @24
    @40
    @22
    c2
    c1
    c2
    cr
    wcel
    @22
    2re
    a1i
    #
    @40
    remulcld
    @22
    c2
    @21
    @42
    @22
    @21
    @33
    nnred
    #
    remulcld
    @22
    c1
    c2
    @41
    clt
    c1
    c2
    clt
    wbr
    @22
    1lt2
    a1i
    2t1e2
    syl6breqr
    @22
    c1
    @21
    c2
    @40
    @43
    @42
    cc0
    c2
    cle
    wbr
    @22
    0le2
    a1i
    @21
    c1
    @4
    elfzle1
    lemul2ad
    ltletrd
    gtned
    subne0d
    mulne0d
    c2
    cz
    wcel
    @22
    2z
    a1i
    expne0d
    divcld
    #
    fvmptd
    @44
    eqeltrd
    adantl
    @21
    cc
    wcel
    vw
    cv
    #
    cc
    wcel
    wa
    @21
    @45
    cmul
    co
    cc
    wcel
    @17
    @21
    @45
    mulcl
    adantl
    seqcl
    #
    @17
    @6
    @17
    @5
    @17
    c2
    @4
    c2
    cn
    wcel
    @17
    2nn
    a1i
    @17
    id
    nnmulcld
    peano2nnd
    nnne0d
    #
    div32d
    @17
    @18
    @17
    @12
    @6
    @46
    @20
    @47
    divcld
    mulid2d
    @17
    @12
    @14
    @6
    cdiv
    vk
    @4
    wallispi2lem2
    oveq1d
    3eqtrd
    mpteq2ia
    vn
    cn
    @16
    @13
    vk
    @4
    wallispi2lem1
    mpteq2ia
    wallispi2.1
    3eqtr4ri
    wallispi
end
