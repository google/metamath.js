include "cvv.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cmpt.mm"
include "df-edg.mm"
include "a1i.mm"
include "fveq2.mm"
include "rneqd.mm"
include "adantl.mm"
include "id.mm"
include "fvex.mm"
include "rnex.mm"
include "fvmptd.mm"
include "wn.mm"
include "c0.mm"
include "rn0.mm"
include "fvprc.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"

theorem edgval
  let cG: class G
  let vg: setvar g


  assert |- ( Edg ` G ) = ran ( iEdg ` G )

  proof
    cG
    cvv
    wcel
    #
    cG
    cedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    wceq
    @0
    vg
    cG
    vg
    cv
    #
    ciedg
    cfv
    #
    crn
    #
    @3
    cvv
    cedg
    cvv
    cedg
    vg
    cvv
    @6
    cmpt
    wceq
    @0
    vg
    df-edg
    a1i
    @4
    cG
    wceq
    #
    @6
    @3
    wceq
    @0
    @7
    @5
    @2
    @4
    cG
    ciedg
    fveq2
    rneqd
    adantl
    @0
    id
    @3
    cvv
    wcel
    @0
    @2
    cG
    ciedg
    fvex
    rnex
    a1i
    fvmptd
    @0
    wn
    #
    c0
    crn
    #
    c0
    @3
    @1
    @9
    c0
    wceq
    @8
    rn0
    a1i
    @8
    @2
    c0
    cG
    ciedg
    fvprc
    rneqd
    cG
    cedg
    fvprc
    3eqtr4rd
    pm2.61i
end
