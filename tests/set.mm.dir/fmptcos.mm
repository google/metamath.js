include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "csbeq1.mm"
include "fmptcof.mm"

theorem fmptcos
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vz: setvar z
  let cT: class T
  assume fmptcof.1: |- ( ph -> A. x e. A R e. B )
  assume fmptcof.2: |- ( ph -> F = ( x e. A |-> R ) )
  assume fmptcof.3: |- ( ph -> G = ( y e. B |-> S ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R y
  disjoint S x
  disjoint A x
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
  disjoint T y
  disjoint T z
  disjoint ph z
  assert |- ( ph -> ( G o. F ) = ( x e. A |-> [_ R / y ]_ S ) )

  proof
    wph
    vx
    vz
    cA
    cB
    cR
    vy
    vz
    cv
    #
    cS
    csb
    #
    vy
    cR
    cS
    csb
    cF
    cG
    fmptcof.1
    fmptcof.2
    wph
    cG
    vy
    cB
    cS
    cmpt
    vz
    cB
    @1
    cmpt
    fmptcof.3
    vy
    vz
    cB
    cS
    @1
    vz
    cS
    nfcv
    vy
    @0
    cS
    nfcsb1v
    vy
    @0
    cS
    csbeq1a
    cbvmpt
    syl6eq
    vy
    @0
    cR
    cS
    csbeq1
    fmptcof
end
