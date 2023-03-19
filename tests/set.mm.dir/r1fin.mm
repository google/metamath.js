include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "r10.mm"
include "0fin.mm"
include "eqeltri.mm"
include "com.mm"
include "cpw.mm"
include "cdm.mm"
include "wlim.mm"
include "wss.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limomss.mm"
include "ax-mp.mm"
include "sseli.mm"
include "r1sucg.mm"
include "syl.mm"
include "pwfi.mm"
include "syl6rbbr.mm"
include "biimpd.mm"
include "finds.mm"

theorem r1fin
  let cA: class A
  let vn: setvar n
  let vm: setvar m


  assert |- ( A e. _om -> ( R1 ` A ) e. Fin )

  proof
    vn
    cv
    #
    cr1
    cfv
    #
    cfn
    wcel
    c0
    cr1
    cfv
    #
    cfn
    wcel
    vm
    cv
    #
    cr1
    cfv
    #
    cfn
    wcel
    #
    @3
    csuc
    #
    cr1
    cfv
    #
    cfn
    wcel
    #
    cA
    cr1
    cfv
    #
    cfn
    wcel
    vn
    vm
    cA
    @0
    c0
    wceq
    @1
    @2
    cfn
    @0
    c0
    cr1
    fveq2
    eleq1d
    @0
    @3
    wceq
    @1
    @4
    cfn
    @0
    @3
    cr1
    fveq2
    eleq1d
    @0
    @6
    wceq
    @1
    @7
    cfn
    @0
    @6
    cr1
    fveq2
    eleq1d
    @0
    cA
    wceq
    @1
    @9
    cfn
    @0
    cA
    cr1
    fveq2
    eleq1d
    @2
    c0
    cfn
    r10
    0fin
    eqeltri
    @3
    com
    wcel
    #
    @5
    @8
    @10
    @8
    @4
    cpw
    #
    cfn
    wcel
    @5
    @10
    @7
    @11
    cfn
    @10
    @3
    cr1
    cdm
    #
    wcel
    @7
    @11
    wceq
    com
    @12
    @3
    @12
    wlim
    #
    com
    @12
    wss
    cr1
    wfun
    @13
    r1funlim
    simpri
    @12
    limomss
    ax-mp
    sseli
    @3
    r1sucg
    syl
    eleq1d
    @4
    pwfi
    syl6rbbr
    biimpd
    finds
end
