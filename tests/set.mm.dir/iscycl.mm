include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "ccycls.mm"
include "cpths.mm"
include "cycls.mm"
include "wa.mm"
include "fveq1.mm"
include "adantl.mm"
include "simpr.mm"
include "fveq2.mm"
include "adantr.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "relpths.mm"
include "brfvopabrbr.mm"

theorem iscycl
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vp: setvar p


  assert |- ( F ( Cycles ` G ) P <-> ( F ( Paths ` G ) P /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) )

  proof
    cc0
    vp
    cv
    #
    cfv
    #
    vf
    cv
    #
    chash
    cfv
    #
    @0
    cfv
    #
    wceq
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    wceq
    vf
    vp
    ccycls
    cpths
    cF
    cP
    cG
    vf
    cG
    vp
    cycls
    @2
    cF
    wceq
    #
    @0
    cP
    wceq
    #
    wa
    #
    @1
    @5
    @4
    @7
    @9
    @1
    @5
    wceq
    @8
    cc0
    @0
    cP
    fveq1
    adantl
    @10
    @3
    @6
    @0
    cP
    @8
    @9
    simpr
    @8
    @3
    @6
    wceq
    @9
    @2
    cF
    chash
    fveq2
    adantr
    fveq12d
    eqeq12d
    cG
    relpths
    brfvopabrbr
end
