include "cv.mm"
include "cfv.mm"
include "cuni.mm"
include "ctop.mm"
include "wcel.mm"
include "ctopon.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wf.mm"
include "cnf.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "fveq2.mm"
include "cnmpt11.mm"

theorem cnmpt11f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cD: class D
  let cM: class M
  let cY: class Y
  let cZ: class Z
  let cP: class P
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt11.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn K ) )
  assume cnmpt11f.f: |- ( ph -> F e. ( K Cn L ) )

  disjoint F x
  disjoint ph x
  disjoint J x
  disjoint X x
  disjoint K x
  disjoint L x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K y
  disjoint L y
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( x e. X |-> ( F ` A ) ) e. ( J Cn L ) )

  proof
    wph
    vx
    vy
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    cJ
    cK
    cL
    cX
    cK
    cuni
    #
    cnmptid.j
    cnmpt11.a
    wph
    cK
    ctop
    wcel
    #
    cK
    @2
    ctopon
    cfv
    wcel
    wph
    vx
    cX
    cA
    cmpt
    #
    cJ
    cK
    ccn
    co
    wcel
    @3
    cnmpt11.a
    @4
    cJ
    cK
    cntop2
    syl
    cK
    @2
    @2
    eqid
    #
    toptopon
    sylib
    wph
    cF
    vy
    @2
    @1
    cmpt
    cK
    cL
    ccn
    co
    #
    wph
    vy
    @2
    cL
    cuni
    #
    cF
    wph
    cF
    @6
    wcel
    @2
    @7
    cF
    wf
    cnmpt11f.f
    cF
    cK
    cL
    @2
    @7
    @5
    @7
    eqid
    cnf
    syl
    feqmptd
    cnmpt11f.f
    eqeltrrd
    @0
    cA
    cF
    fveq2
    cnmpt11
end
