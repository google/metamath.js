include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cfl.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "ccht.mm"
include "c2.mm"
include "cfz.mm"
include "flidm.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "wceq.mm"
include "reflcl.mm"
include "ppisval.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "sumeq1d.mm"
include "chtval.mm"

theorem chtfl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. RR -> ( theta ` ( |_ ` A ) ) = ( theta ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cfl
    cfv
    #
    cicc
    co
    cprime
    cin
    #
    vp
    cv
    clog
    cfv
    #
    vp
    csu
    #
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    @3
    vp
    csu
    @1
    ccht
    cfv
    #
    cA
    ccht
    cfv
    @0
    @2
    @5
    @3
    vp
    @0
    c2
    @1
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    c2
    @1
    cfz
    co
    #
    cprime
    cin
    @2
    @5
    @0
    @8
    @10
    cprime
    @0
    @7
    @1
    c2
    cfz
    cA
    flidm
    oveq2d
    ineq1d
    @0
    @1
    cr
    wcel
    #
    @2
    @9
    wceq
    cA
    reflcl
    #
    @1
    ppisval
    syl
    cA
    ppisval
    3eqtr4d
    sumeq1d
    @0
    @11
    @6
    @4
    wceq
    @12
    @1
    vp
    chtval
    syl
    cA
    vp
    chtval
    3eqtr4d
end
