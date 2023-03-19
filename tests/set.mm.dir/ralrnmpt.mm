include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "cv.mm"
include "cfv.mm"
include "wsbc.mm"
include "wfn.mm"
include "wb.mm"
include "fnmpt.mm"
include "dfsbcq.mm"
include "ralrn.mm"
include "syl.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "sbceq1a.mm"
include "cbvral.mm"
include "bicomi.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfsbc.mm"
include "weq.mm"
include "fveq2.mm"
include "sbceq1d.mm"
include "3bitr3g.mm"
include "wa.mm"
include "fvmpt2.mm"
include "sbcieg.mm"
include "adantl.mm"
include "bitrd.mm"
include "ralimiaa.mm"
include "ralbi.mm"

theorem ralrnmpt
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  assume ralrnmpt.1: |- F = ( x e. A |-> B )
  assume ralrnmpt.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint A x
  disjoint B y
  disjoint ch y
  disjoint F y
  disjoint ps x
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint w y
  disjoint F w
  disjoint y z
  disjoint F z
  disjoint ps w
  disjoint ps z
  assert |- ( A. x e. A B e. V -> ( A. y e. ran F ps <-> A. x e. A ch ) )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    #
    wps
    vy
    cF
    crn
    #
    wral
    #
    wps
    vy
    vx
    cv
    #
    cF
    cfv
    #
    wsbc
    #
    vx
    cA
    wral
    #
    wch
    vx
    cA
    wral
    #
    @1
    wps
    vy
    vw
    cv
    #
    wsbc
    #
    vw
    @2
    wral
    #
    wps
    vy
    vz
    cv
    #
    cF
    cfv
    #
    wsbc
    #
    vz
    cA
    wral
    #
    @3
    @7
    @1
    cF
    cA
    wfn
    @11
    @15
    wb
    vx
    cA
    cB
    cF
    cV
    ralrnmpt.1
    fnmpt
    @10
    @14
    vw
    vz
    cA
    cF
    wps
    vy
    @9
    @13
    dfsbcq
    ralrn
    syl
    @3
    @11
    wps
    @10
    vy
    vw
    @2
    wps
    vw
    nfv
    wps
    vy
    @9
    nfsbc1v
    wps
    vy
    @9
    sbceq1a
    cbvral
    bicomi
    @14
    @6
    vz
    vx
    cA
    wps
    vx
    vy
    @13
    vx
    @12
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    ralrnmpt.1
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    vx
    @12
    nfcv
    nffv
    wps
    vx
    nfv
    nfsbc
    @6
    vz
    nfv
    vz
    vx
    weq
    wps
    vy
    @13
    @5
    @12
    @4
    cF
    fveq2
    sbceq1d
    cbvral
    3bitr3g
    @1
    @6
    wch
    wb
    #
    vx
    cA
    wral
    @7
    @8
    wb
    @0
    @16
    vx
    cA
    @4
    cA
    wcel
    #
    @0
    wa
    #
    @6
    wps
    vy
    cB
    wsbc
    #
    wch
    @18
    wps
    vy
    @5
    cB
    vx
    cA
    cB
    cV
    cF
    ralrnmpt.1
    fvmpt2
    sbceq1d
    @0
    @19
    wch
    wb
    @17
    wps
    wch
    vy
    cB
    cV
    ralrnmpt.2
    sbcieg
    adantl
    bitrd
    ralimiaa
    @6
    wch
    vx
    cA
    ralbi
    syl
    bitrd
end
