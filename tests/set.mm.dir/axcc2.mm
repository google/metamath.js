include "com.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cxp.mm"
include "c2nd.mm"
include "nfcv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ifbieq2d.mm"
include "cbvmpt.mm"
include "nffvmpt1.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "nffv.mm"
include "fveq2d.mm"
include "axcc2lem.mm"

theorem axcc2
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vf: setvar f
  let vm: setvar m

  disjoint F g
  disjoint F n
  disjoint g n
  disjoint F f
  disjoint F m
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint g m
  disjoint m n
  assert |- E. g ( g Fn _om /\ A. n e. _om ( ( F ` n ) =/= (/) -> ( g ` n ) e. ( F ` n ) ) )

  proof
    vm
    com
    vm
    cv
    #
    csn
    #
    @0
    vm
    com
    @0
    cF
    cfv
    #
    c0
    wceq
    #
    c0
    csn
    #
    @2
    cif
    #
    cmpt
    #
    cfv
    #
    cxp
    #
    cmpt
    #
    vf
    vg
    vn
    cF
    vm
    com
    @0
    @9
    cfv
    #
    vf
    cv
    #
    cfv
    #
    c2nd
    cfv
    #
    cmpt
    @6
    vm
    vn
    com
    @5
    vn
    cv
    #
    cF
    cfv
    #
    c0
    wceq
    #
    @4
    @15
    cif
    #
    vn
    @5
    nfcv
    vm
    @17
    nfcv
    @0
    @14
    wceq
    #
    @3
    @16
    @2
    @15
    @4
    @18
    @2
    @15
    c0
    @0
    @14
    cF
    fveq2
    #
    eqeq1d
    @19
    ifbieq2d
    cbvmpt
    vm
    vn
    com
    @8
    @14
    csn
    #
    @14
    @6
    cfv
    #
    cxp
    vn
    @8
    nfcv
    vm
    @20
    @21
    vm
    @20
    nfcv
    vm
    com
    @5
    @14
    nffvmpt1
    nfxp
    @18
    @1
    @20
    @7
    @21
    @0
    @14
    sneq
    @0
    @14
    @6
    fveq2
    xpeq12d
    cbvmpt
    vm
    vn
    com
    @13
    @14
    @9
    cfv
    #
    @11
    cfv
    #
    c2nd
    cfv
    vn
    @13
    nfcv
    vm
    @23
    c2nd
    vm
    c2nd
    nfcv
    vm
    @22
    @11
    vm
    @11
    nfcv
    vm
    com
    @8
    @14
    nffvmpt1
    nffv
    nffv
    @18
    @12
    @23
    c2nd
    @18
    @10
    @22
    @11
    @0
    @14
    @9
    fveq2
    fveq2d
    fveq2d
    cbvmpt
    axcc2lem
end
