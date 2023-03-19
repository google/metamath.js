include "c1st.mm"
include "cfv.mm"
include "cpg.mm"
include "wss.mm"
include "c2nd.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "cun.mm"
include "wceq.mm"
include "wi.mm"
include "fvex.mm"
include "unex.mm"
include "isseti.mm"
include "sseq1.mm"
include "unss.mm"
include "syl6bbr.mm"
include "biimprd.mm"
include "ssun1.mm"
include "id.mm"
include "syl5sseqr.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ssun2.mm"
include "jca.mm"
include "jctird.mm"
include "eximii.mm"
include "19.37iv.mm"

theorem elpglem2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint x y
  disjoint k x
  assert |- ( ( ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg ) -> E. x ( x C_ Pg /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) ) )

  proof
    cA
    c1st
    cfv
    #
    cpg
    wss
    cA
    c2nd
    cfv
    #
    cpg
    wss
    wa
    #
    vx
    cv
    #
    cpg
    wss
    #
    @0
    @3
    cpw
    #
    wcel
    #
    @1
    @5
    wcel
    #
    wa
    #
    wa
    #
    vx
    @3
    @0
    @1
    cun
    #
    wceq
    #
    @2
    @9
    wi
    vx
    vx
    @10
    @0
    @1
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    unex
    isseti
    @11
    @2
    @4
    @8
    @11
    @4
    @2
    @11
    @4
    @10
    cpg
    wss
    @2
    @3
    @10
    cpg
    sseq1
    @0
    @1
    cpg
    unss
    syl6bbr
    biimprd
    @11
    @6
    @7
    @11
    @0
    @3
    wss
    @6
    @11
    @10
    @0
    @3
    @0
    @1
    ssun1
    @11
    id
    #
    syl5sseqr
    @0
    @3
    vx
    vex
    #
    elpw2
    sylibr
    @11
    @1
    @3
    wss
    @7
    @11
    @10
    @1
    @3
    @1
    @0
    ssun2
    @12
    syl5sseqr
    @1
    @3
    @13
    elpw2
    sylibr
    jca
    jctird
    eximii
    19.37iv
end
