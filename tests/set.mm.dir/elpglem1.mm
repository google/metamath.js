include "cv.mm"
include "cpg.mm"
include "wss.mm"
include "c1st.mm"
include "cfv.mm"
include "cpw.mm"
include "wcel.mm"
include "c2nd.mm"
include "wa.mm"
include "elpwi.mm"
include "adantl.mm"
include "simpl.mm"
include "sstrd.mm"
include "anim12dan.mm"
include "exlimiv.mm"

theorem elpglem1
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint x y
  disjoint k x
  assert |- ( E. x ( x C_ Pg /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) ) -> ( ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg ) )

  proof
    vx
    cv
    #
    cpg
    wss
    #
    cA
    c1st
    cfv
    #
    @0
    cpw
    #
    wcel
    #
    cA
    c2nd
    cfv
    #
    @3
    wcel
    #
    wa
    wa
    @2
    cpg
    wss
    #
    @5
    cpg
    wss
    #
    wa
    vx
    @1
    @4
    @7
    @6
    @8
    @1
    @4
    wa
    @2
    @0
    cpg
    @4
    @2
    @0
    wss
    @1
    @2
    @0
    elpwi
    adantl
    @1
    @4
    simpl
    sstrd
    @1
    @6
    wa
    @5
    @0
    cpg
    @6
    @5
    @0
    wss
    @1
    @5
    @0
    elpwi
    adantl
    @1
    @6
    simpl
    sstrd
    anim12dan
    exlimiv
end
