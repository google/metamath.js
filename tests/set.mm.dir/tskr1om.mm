include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cr1.mm"
include "com.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "csuc.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "r10.mm"
include "tsk0.mm"
include "syl5eqel.mm"
include "cpw.mm"
include "tskpw.mm"
include "con0.mm"
include "nnon.mm"
include "r1suc.mm"
include "syl.mm"
include "syl5ibr.mm"
include "expd.mm"
include "adantrd.mm"
include "finds2.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "wfun.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "syl11.mm"
include "ssrdv.mm"

theorem tskr1om
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> ( R1 " _om ) C_ T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    #
    wa
    #
    vy
    cr1
    com
    cima
    #
    cT
    vx
    cv
    #
    cr1
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vx
    com
    wrex
    #
    @2
    @6
    cT
    wcel
    #
    @6
    @3
    wcel
    #
    @7
    @2
    @9
    wi
    #
    vx
    com
    @4
    com
    wcel
    @2
    @5
    cT
    wcel
    #
    wi
    @7
    @11
    @12
    c0
    cr1
    cfv
    #
    cT
    wcel
    @6
    cr1
    cfv
    #
    cT
    wcel
    #
    @6
    csuc
    #
    cr1
    cfv
    #
    cT
    wcel
    #
    @2
    vx
    vy
    @4
    c0
    wceq
    @5
    @13
    cT
    @4
    c0
    cr1
    fveq2
    eleq1d
    @4
    @6
    wceq
    @5
    @14
    cT
    @4
    @6
    cr1
    fveq2
    eleq1d
    @4
    @16
    wceq
    @5
    @17
    cT
    @4
    @16
    cr1
    fveq2
    eleq1d
    @2
    @13
    c0
    cT
    r10
    cT
    tsk0
    syl5eqel
    @6
    com
    wcel
    #
    @0
    @15
    @18
    wi
    @1
    @19
    @0
    @15
    @18
    @0
    @15
    wa
    @18
    @19
    @14
    cpw
    #
    cT
    wcel
    @14
    cT
    tskpw
    @19
    @17
    @20
    cT
    @19
    @6
    con0
    wcel
    @17
    @20
    wceq
    @6
    nnon
    @6
    r1suc
    syl
    eleq1d
    syl5ibr
    expd
    adantrd
    finds2
    @7
    @12
    @9
    @2
    @5
    @6
    cT
    eleq1
    imbi2d
    syl5ibcom
    rexlimiv
    cr1
    wfun
    #
    @10
    @8
    cr1
    con0
    wfn
    @21
    r1fnon
    con0
    cr1
    fnfun
    ax-mp
    vx
    @6
    com
    cr1
    fvelima
    mpan
    syl11
    ssrdv
end
