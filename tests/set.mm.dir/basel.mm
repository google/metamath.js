include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "cmul.mm"
include "cdiv.mm"
include "cpi.mm"
include "c6.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "eqid.mm"
include "basellem9.mm"

theorem basel
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- sum_ k e. NN ( k ^ -u 2 ) = ( ( _pi ^ 2 ) / 6 )

  proof
    vk
    vn
    caddc
    vm
    cn
    vm
    cv
    #
    c2
    cneg
    #
    cexp
    co
    #
    cmpt
    #
    c1
    cseq
    #
    vm
    cn
    c1
    c2
    @0
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
    cn
    cpi
    c2
    cexp
    co
    c6
    cdiv
    co
    csn
    cxp
    cn
    c1
    csn
    cxp
    #
    @8
    cmin
    cof
    co
    cmul
    cof
    #
    co
    #
    @11
    @9
    cn
    @1
    csn
    cxp
    @8
    @10
    co
    caddc
    cof
    #
    co
    @10
    co
    #
    @11
    @9
    @8
    @12
    co
    @10
    co
    #
    vm
    vn
    cn
    @7
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
    @0
    @15
    wceq
    #
    @6
    @17
    c1
    cdiv
    @18
    @5
    @16
    c1
    caddc
    @0
    @15
    c2
    cmul
    oveq2
    oveq1d
    oveq2d
    cbvmptv
    @3
    vn
    cn
    @15
    @1
    cexp
    co
    #
    cmpt
    #
    wceq
    @4
    caddc
    @20
    c1
    cseq
    wceq
    vm
    vn
    cn
    @2
    @19
    @0
    @15
    @1
    cexp
    oveq1
    cbvmptv
    caddc
    @3
    @20
    c1
    seqeq3
    ax-mp
    @11
    eqid
    @13
    eqid
    @14
    eqid
    basellem9
end
