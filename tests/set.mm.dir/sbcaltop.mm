include "caltop.mm"
include "csb.mm"
include "cvv.mm"
include "wnfc.mm"
include "wcel.mm"
include "nfcsb1v.mm"
include "nfaltop.mm"
include "a1i.mm"
include "cv.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "altopeq1.mm"
include "syl.mm"
include "altopeq2.mm"
include "eqtrd.mm"
include "csbiegf.mm"

theorem sbcaltop
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D

  disjoint A x
  assert |- ( A e. _V -> [_ A / x ]_ << C , D >> = << [_ A / x ]_ C , [_ A / x ]_ D >> )

  proof
    vx
    cA
    cC
    cD
    caltop
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cD
    csb
    #
    caltop
    #
    cvv
    vx
    @3
    wnfc
    cA
    cvv
    wcel
    vx
    @1
    @2
    vx
    cA
    cC
    nfcsb1v
    vx
    cA
    cD
    nfcsb1v
    nfaltop
    a1i
    vx
    cv
    cA
    wceq
    #
    @0
    @1
    cD
    caltop
    #
    @3
    @4
    cC
    @1
    wceq
    @0
    @5
    wceq
    vx
    cA
    cC
    csbeq1a
    cC
    @1
    cD
    altopeq1
    syl
    @4
    cD
    @2
    wceq
    @5
    @3
    wceq
    vx
    cA
    cD
    csbeq1a
    cD
    @2
    @1
    altopeq2
    syl
    eqtrd
    csbiegf
end
