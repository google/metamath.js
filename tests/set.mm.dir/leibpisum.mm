include "cn0.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "caddc.mm"
include "cdiv.mm"
include "csu.mm"
include "cpi.mm"
include "c4.mm"
include "wceq.mm"
include "wtru.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "cfv.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cc.mm"
include "cr.mm"
include "neg1rr.mm"
include "reexpcl.mm"
include "mpan.mm"
include "cn.mm"
include "2nn0.mm"
include "nn0mulcl.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "nndivred.mm"
include "recnd.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "leibpi.mm"
include "a1i.mm"
include "isumclim.mm"
include "trud.mm"

theorem leibpisum
  let vn: setvar n
  let vk: setvar k


  assert |- sum_ n e. NN0 ( ( -u 1 ^ n ) / ( ( 2 x. n ) + 1 ) ) = ( _pi / 4 )

  proof
    cn0
    c1
    cneg
    #
    vn
    cv
    #
    cexp
    co
    #
    c2
    @1
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    vn
    csu
    cpi
    c4
    cdiv
    co
    #
    wceq
    wtru
    @5
    @6
    vn
    vk
    cn0
    @0
    vk
    cv
    #
    cexp
    co
    #
    c2
    @7
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    cn0
    nn0uz
    wtru
    0zd
    @1
    cn0
    wcel
    #
    @1
    @12
    cfv
    @5
    wceq
    wtru
    vk
    @1
    @11
    @5
    cn0
    @12
    @7
    @1
    wceq
    #
    @8
    @2
    @10
    @4
    cdiv
    @7
    @1
    @0
    cexp
    oveq2
    @14
    @9
    @3
    c1
    caddc
    @7
    @1
    c2
    cmul
    oveq2
    oveq1d
    oveq12d
    @12
    eqid
    #
    @2
    @4
    cdiv
    ovex
    fvmpt
    adantl
    @13
    @5
    cc
    wcel
    wtru
    @13
    @5
    @13
    @2
    @4
    @0
    cr
    wcel
    @13
    @2
    cr
    wcel
    neg1rr
    @0
    @1
    reexpcl
    mpan
    @13
    @3
    cn0
    wcel
    #
    @4
    cn
    wcel
    c2
    cn0
    wcel
    @13
    @16
    2nn0
    c2
    @1
    nn0mulcl
    mpan
    @3
    nn0p1nn
    syl
    nndivred
    recnd
    adantl
    caddc
    @12
    cc0
    cseq
    @6
    cli
    wbr
    wtru
    vk
    @12
    @15
    leibpi
    a1i
    isumclim
    trud
end
