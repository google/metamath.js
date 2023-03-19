include "ccom.mm"
include "csb.mm"
include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "csbeq1.mm"
include "fmptco.mm"
include "nfcsb.mm"
include "csbeq1d.mm"
include "syl6eqr.mm"
include "eqid.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "ralimi.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "syl.mm"
include "eqtrd.mm"

theorem fmptcof
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vz: setvar z
  assume fmptcof.1: |- ( ph -> A. x e. A R e. B )
  assume fmptcof.2: |- ( ph -> F = ( x e. A |-> R ) )
  assume fmptcof.3: |- ( ph -> G = ( y e. B |-> S ) )
  assume fmptcof.4: |- ( y = R -> S = T )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R y
  disjoint S x
  disjoint A x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint R w
  disjoint R z
  disjoint S w
  disjoint S z
  disjoint A z
  disjoint T z
  disjoint ph z
  assert |- ( ph -> ( G o. F ) = ( x e. A |-> T ) )

  proof
    wph
    cG
    cF
    ccom
    #
    vx
    cA
    vy
    cR
    cS
    csb
    #
    cmpt
    #
    vx
    cA
    cT
    cmpt
    #
    wph
    @0
    vz
    cA
    vy
    vx
    vz
    cv
    #
    cR
    csb
    #
    cS
    csb
    #
    cmpt
    @2
    wph
    vz
    vw
    cA
    cB
    @5
    vy
    vw
    cv
    #
    cS
    csb
    #
    @6
    cF
    cG
    wph
    cR
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @4
    cA
    wcel
    @5
    cB
    wcel
    #
    fmptcof.1
    @9
    @11
    vx
    @4
    cA
    vx
    @5
    cB
    vx
    @4
    cR
    nfcsb1v
    #
    nfel1
    vx
    cv
    @4
    wceq
    #
    cR
    @5
    cB
    vx
    @4
    cR
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    wph
    cF
    vx
    cA
    cR
    cmpt
    vz
    cA
    @5
    cmpt
    fmptcof.2
    vx
    vz
    cA
    cR
    @5
    vz
    cR
    nfcv
    @12
    @14
    cbvmpt
    syl6eq
    wph
    cG
    vy
    cB
    cS
    cmpt
    vw
    cB
    @8
    cmpt
    fmptcof.3
    vy
    vw
    cB
    cS
    @8
    vw
    cS
    nfcv
    vy
    @7
    cS
    nfcsb1v
    vy
    @7
    cS
    csbeq1a
    cbvmpt
    syl6eq
    vy
    @7
    @5
    cS
    csbeq1
    fmptco
    vx
    vz
    cA
    @1
    @6
    vz
    @1
    nfcv
    vx
    vy
    @5
    cS
    @12
    vx
    cS
    nfcv
    nfcsb
    @13
    vy
    cR
    @5
    cS
    @14
    csbeq1d
    cbvmpt
    syl6eqr
    wph
    @10
    @2
    @3
    wceq
    #
    fmptcof.1
    @10
    cA
    cA
    wceq
    @1
    cT
    wceq
    #
    vx
    cA
    wral
    @15
    cA
    eqid
    @9
    @16
    vx
    cA
    vy
    cR
    cS
    cT
    cB
    @9
    vy
    cT
    nfcvd
    fmptcof.4
    csbiegf
    ralimi
    vx
    cA
    @1
    cA
    cT
    mpteq12
    sylancr
    syl
    eqtrd
end
