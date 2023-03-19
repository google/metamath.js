include "cv.mm"
include "csb.mm"
include "nfv.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "wcel.mm"
include "wa.mm"
include "wsb.mm"
include "sbimi.mm"
include "nfel.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "sbie.mm"
include "eleq1d.mm"
include "3imtr3i.mm"
include "csbeq1.mm"
include "funcnv5mpt.mm"

theorem funcnv4mpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume funcnvmpt.0: |- F/ x ph
  assume funcnvmpt.1: |- F/_ x A
  assume funcnvmpt.2: |- F/_ x F
  assume funcnvmpt.3: |- F = ( x e. A |-> B )
  assume funcnvmpt.4: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint i j
  disjoint i x
  disjoint j x
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint F i
  disjoint V x
  disjoint i ph
  disjoint j ph
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( Fun `' F <-> A. i e. A A. j e. A ( i = j \/ [_ i / x ]_ B =/= [_ j / x ]_ B ) ) )

  proof
    wph
    vi
    vj
    cA
    vx
    vi
    cv
    #
    cB
    csb
    #
    vx
    vj
    cv
    #
    cB
    csb
    cF
    cV
    wph
    vi
    nfv
    vi
    cA
    nfcv
    #
    vi
    cF
    nfcv
    cF
    vx
    cA
    cB
    cmpt
    vi
    cA
    @1
    cmpt
    funcnvmpt.3
    vx
    vi
    cA
    cB
    @1
    funcnvmpt.1
    @3
    vi
    cB
    nfcv
    vx
    @0
    cB
    nfcsb1v
    #
    vx
    @0
    cB
    csbeq1a
    #
    cbvmptf
    eqtri
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vx
    vi
    wsb
    cB
    cV
    wcel
    #
    vx
    vi
    wsb
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    cV
    wcel
    #
    @8
    @9
    vx
    vi
    funcnvmpt.4
    sbimi
    @8
    @11
    vx
    vi
    wph
    @10
    vx
    funcnvmpt.0
    vx
    @0
    cA
    vx
    @0
    nfcv
    funcnvmpt.1
    nfel
    nfan
    vx
    vi
    weq
    #
    @7
    @10
    wph
    @6
    @0
    cA
    eleq1
    anbi2d
    sbie
    @9
    @12
    vx
    vi
    vx
    @1
    cV
    @4
    vx
    cV
    nfcv
    nfel
    @13
    cB
    @1
    cV
    @5
    eleq1d
    sbie
    3imtr3i
    vx
    @0
    @2
    cB
    csbeq1
    funcnv5mpt
end
