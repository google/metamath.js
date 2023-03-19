include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt.mm"
include "cfa.mm"
include "crli.mm"
include "cn0.mm"
include "wcel.mm"
include "wbr.mm"
include "1nn0.mm"
include "logexprlim.mm"
include "ax-mp.mm"
include "wa.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "relogcld.mm"
include "recnd.mm"
include "exp1d.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "rpcn.mm"
include "rpne0.mm"
include "fsumdivc.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "fac1.mm"
include "3brtr3i.mm"

theorem logfacrlim2
  let vx: setvar x
  let vn: setvar n
  let cA: class A
  let vk: setvar k
  let vy: setvar y
  let cN: class N

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( x e. RR+ |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( log ` ( x / n ) ) / x ) ) ~~>r 1

  proof
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @0
    vn
    cv
    #
    cdiv
    co
    #
    clog
    cfv
    #
    c1
    cexp
    co
    #
    vn
    csu
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    c1
    cfa
    cfv
    #
    vx
    crp
    @2
    @5
    @0
    cdiv
    co
    vn
    csu
    #
    cmpt
    c1
    crli
    c1
    cn0
    wcel
    @9
    @10
    crli
    wbr
    1nn0
    vx
    vn
    c1
    logexprlim
    ax-mp
    vx
    crp
    @8
    @11
    @0
    crp
    wcel
    #
    @8
    @2
    @5
    vn
    csu
    #
    @0
    cdiv
    co
    @11
    @12
    @7
    @13
    @0
    cdiv
    @12
    @2
    @6
    @5
    vn
    @12
    @3
    @2
    wcel
    #
    wa
    #
    @5
    @15
    @5
    @15
    @4
    @14
    @12
    @3
    crp
    wcel
    @4
    crp
    wcel
    @14
    @3
    @3
    @1
    elfznn
    nnrpd
    @0
    @3
    rpdivcl
    sylan2
    relogcld
    recnd
    #
    exp1d
    sumeq2dv
    oveq1d
    @12
    @2
    @5
    @0
    vn
    @12
    c1
    @1
    fzfid
    @0
    rpcn
    @16
    @0
    rpne0
    fsumdivc
    eqtrd
    mpteq2ia
    fac1
    3brtr3i
end
