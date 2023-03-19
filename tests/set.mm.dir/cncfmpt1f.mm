include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "wcel.mm"
include "wral.mm"
include "cncff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptcof.mm"
include "cncfco.mm"
include "eqeltrrd.mm"

theorem cncfmpt1f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vy: setvar y
  assume cncfmpt1f.1: |- ( ph -> F e. ( CC -cn-> CC ) )
  assume cncfmpt1f.2: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> CC ) )

  disjoint F x
  disjoint ph x
  disjoint X x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- ( ph -> ( x e. X |-> ( F ` A ) ) e. ( X -cn-> CC ) )

  proof
    wph
    cF
    vx
    cX
    cA
    cmpt
    #
    ccom
    vx
    cX
    cA
    cF
    cfv
    #
    cmpt
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    vy
    cX
    cc
    cA
    vy
    cv
    #
    cF
    cfv
    @1
    @0
    cF
    wph
    cX
    cc
    @0
    wf
    #
    cA
    cc
    wcel
    vx
    cX
    wral
    wph
    @0
    @2
    wcel
    @4
    cncfmpt1f.2
    cX
    cc
    @0
    cncff
    syl
    vx
    cX
    cc
    cA
    @0
    @0
    eqid
    fmpt
    sylibr
    wph
    @0
    eqidd
    wph
    vy
    cc
    cc
    cF
    wph
    cF
    cc
    cc
    ccncf
    co
    wcel
    cc
    cc
    cF
    wf
    cncfmpt1f.1
    cc
    cc
    cF
    cncff
    syl
    feqmptd
    @3
    cA
    cF
    fveq2
    fmptcof
    wph
    cX
    cc
    cc
    @0
    cF
    cncfmpt1f.2
    cncfmpt1f.1
    cncfco
    eqeltrrd
end
