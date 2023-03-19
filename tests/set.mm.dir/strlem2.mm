include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cch.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem strlem2
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cS: class S
  assume strlem2.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )

  disjoint C x
  disjoint u x
  assert |- ( C e. CH -> ( S ` C ) = ( ( normh ` ( ( projh ` C ) ` u ) ) ^ 2 ) )

  proof
    vx
    cC
    vu
    cv
    #
    vx
    cv
    #
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    @0
    cC
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    cch
    cS
    @1
    cC
    wceq
    #
    @4
    @7
    c2
    cexp
    @8
    @3
    @6
    cno
    @8
    @0
    @2
    @5
    @1
    cC
    cpjh
    fveq2
    fveq1d
    fveq2d
    oveq1d
    strlem2.1
    @7
    c2
    cexp
    ovex
    fvmpt
end
