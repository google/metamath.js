include "cdm.mm"
include "cc.mm"
include "dmmptd.mm"
include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "climc.mm"
include "co.mm"
include "w3a.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"

theorem limcmptdm
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume limcmptdm.f: |- F = ( x e. A |-> B )
  assume limcmptdm.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume limcmptdm.c: |- ( ph -> C e. ( F limCC D ) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> A C_ CC )

  proof
    wph
    cA
    cF
    cdm
    #
    cc
    wph
    vx
    cF
    cA
    cB
    cc
    limcmptdm.f
    limcmptdm.b
    dmmptd
    wph
    @0
    cc
    cF
    wf
    #
    @0
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    cC
    cF
    cD
    climc
    co
    wcel
    @1
    @2
    @3
    w3a
    limcmptdm.c
    cD
    cC
    cF
    limcrcl
    syl
    simp2d
    eqsstr3d
end
