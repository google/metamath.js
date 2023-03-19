include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "cr.mm"
include "cn.mm"
include "csup.mm"
include "cmpt.mm"
include "weq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "oveq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "breq2.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rpnnen1lem6.mm"

theorem rpnnen1
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume rpnnen1.n: |- NN e. _V
  assume rpnnen1.q: |- QQ e. _V


  assert |- RR ~<_ ( QQ ^m NN )

  proof
    vx
    vm
    cv
    #
    vk
    cv
    #
    cdiv
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vm
    cz
    crab
    #
    vk
    vn
    vy
    cr
    vj
    cn
    @0
    vj
    cv
    #
    cdiv
    co
    #
    vy
    cv
    #
    clt
    wbr
    #
    vm
    cz
    crab
    #
    cr
    clt
    csup
    #
    @6
    cdiv
    co
    #
    cmpt
    #
    cmpt
    @4
    vn
    cv
    #
    @1
    cdiv
    co
    #
    @3
    clt
    wbr
    vm
    vn
    cz
    vm
    vn
    weq
    @2
    @15
    @3
    clt
    @0
    @14
    @1
    cdiv
    oveq1
    breq1d
    cbvrabv
    vy
    vx
    cr
    @13
    vk
    cn
    @5
    cr
    clt
    csup
    #
    @1
    cdiv
    co
    #
    cmpt
    #
    vy
    vx
    weq
    #
    @13
    vk
    cn
    @2
    @8
    clt
    wbr
    #
    vm
    cz
    crab
    #
    cr
    clt
    csup
    #
    @1
    cdiv
    co
    #
    cmpt
    @18
    vj
    vk
    cn
    @12
    @23
    vj
    vk
    weq
    #
    @11
    @22
    @6
    @1
    cdiv
    @24
    cr
    @10
    @21
    clt
    @24
    @9
    @20
    vm
    cz
    @24
    @7
    @2
    @8
    clt
    @6
    @1
    @0
    cdiv
    oveq2
    breq1d
    rabbidv
    supeq1d
    @24
    id
    oveq12d
    cbvmptv
    @19
    vk
    cn
    @23
    @17
    @19
    @22
    @16
    @1
    cdiv
    @19
    cr
    @21
    @5
    clt
    @19
    @20
    @4
    vm
    cz
    @8
    @3
    @2
    clt
    breq2
    rabbidv
    supeq1d
    oveq1d
    mpteq2dv
    syl5eq
    cbvmptv
    rpnnen1.n
    rpnnen1.q
    rpnnen1lem6
end
