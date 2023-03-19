include "wfun.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wlim.mm"
include "wo.mm"
include "wn.mm"
include "cuni.mm"
include "cfv.mm"
include "crn.mm"
include "w3o.mm"
include "copab.mm"
include "wmo.mm"
include "funopab.mm"
include "fvex.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "rnexg.mm"
include "uniexg.mm"
include "mp2b.mm"
include "nlim0.mm"
include "wb.mm"
include "dm0.mm"
include "limeq.mm"
include "ax-mp.mm"
include "mtbir.mm"
include "dmeq.mm"
include "syl.mm"
include "biimpa.mm"
include "mto.mm"
include "moeq3.mm"
include "mpgbir.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem tz7.44lem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cG: class G
  let cH: class H
  assume tz7.44lem1.1: |- G = { <. x , y >. | ( ( x = (/) /\ y = A ) \/ ( -. ( x = (/) \/ Lim dom x ) /\ y = ( H ` ( x ` U. dom x ) ) ) \/ ( Lim dom x /\ y = U. ran x ) ) }

  disjoint x y
  disjoint A y
  disjoint H y
  assert |- Fun G

  proof
    cG
    wfun
    vx
    cv
    #
    c0
    wceq
    #
    vy
    cv
    #
    cA
    wceq
    wa
    @1
    @0
    cdm
    #
    wlim
    #
    wo
    wn
    @2
    @3
    cuni
    @0
    cfv
    #
    cH
    cfv
    #
    wceq
    wa
    @4
    @2
    @0
    crn
    #
    cuni
    #
    wceq
    wa
    w3o
    #
    vx
    vy
    copab
    #
    wfun
    #
    @11
    @9
    vy
    wmo
    vx
    @9
    vx
    vy
    funopab
    @1
    @4
    vy
    cA
    @6
    @8
    @5
    cH
    fvex
    @0
    cvv
    wcel
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    vx
    vex
    @0
    cvv
    rnexg
    @7
    cvv
    uniexg
    mp2b
    @1
    @4
    wa
    c0
    cdm
    #
    wlim
    #
    @13
    c0
    wlim
    #
    nlim0
    @12
    c0
    wceq
    @13
    @14
    wb
    dm0
    @12
    c0
    limeq
    ax-mp
    mtbir
    @1
    @4
    @13
    @1
    @3
    @12
    wceq
    @4
    @13
    wb
    @0
    c0
    dmeq
    @3
    @12
    limeq
    syl
    biimpa
    mto
    moeq3
    mpgbir
    cG
    @10
    tz7.44lem1.1
    funeqi
    mpbir
end
