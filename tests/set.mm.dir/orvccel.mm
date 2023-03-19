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
include "ccld.mm"
include "wcel.mm"
include "wss.mm"
include "cldssbrsiga.mm"
include "syl.mm"
include "sseldd.mm"
include "mbfmcnvima.mm"
include "eqeltrd.mm"

theorem orvccel
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
  assume orvccel.5: |- ( ph -> { y e. U. J | y R A } e. ( Clsd ` J ) )

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
    ccld
    cfv
    #
    @1
    @0
    wph
    cJ
    ctop
    wcel
    @2
    @1
    wss
    orvccel.2
    cJ
    cldssbrsiga
    syl
    orvccel.5
    sseldd
    mbfmcnvima
    eqeltrd
end
