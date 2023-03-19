include "corvc.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "cuni.mm"
include "crab.mm"
include "cima.mm"
include "orvcval4.mm"
include "csigagen.mm"
include "cfv.mm"
include "ctop.mm"
include "sgsiga.mm"
include "wcel.mm"
include "wss.mm"
include "sssigagen.mm"
include "syl.mm"
include "sseldd.mm"
include "mbfmcnvima.mm"
include "eqeltrd.mm"

theorem orvcoel
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cJ: class J
  let cV: class V
  let cX: class X
  assume orvccel.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume orvccel.2: |- ( ph -> J e. Top )
  assume orvccel.3: |- ( ph -> X e. ( S MblFnM ( sigaGen ` J ) ) )
  assume orvccel.4: |- ( ph -> A e. V )
  assume orvcoel.5: |- ( ph -> { y e. U. J | y R A } e. J )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint J y
  assert |- ( ph -> ( X oRVC R A ) e. S )

  proof
    wph
    cX
    cA
    cR
    corvc
    co
    cX
    ccnv
    vy
    cv
    cA
    cR
    wbr
    vy
    cJ
    cuni
    crab
    #
    cima
    cS
    wph
    vy
    cA
    cR
    cS
    cJ
    cV
    cX
    orvccel.1
    orvccel.2
    orvccel.3
    orvccel.4
    orvcval4
    wph
    @0
    cS
    cJ
    csigagen
    cfv
    #
    cX
    orvccel.1
    wph
    cJ
    ctop
    orvccel.2
    sgsiga
    orvccel.3
    wph
    cJ
    @1
    @0
    wph
    cJ
    ctop
    wcel
    cJ
    @1
    wss
    orvccel.2
    cJ
    ctop
    sssigagen
    syl
    orvcoel.5
    sseldd
    mbfmcnvima
    eqeltrd
end
