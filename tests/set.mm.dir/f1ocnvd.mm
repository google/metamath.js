include "wf1o.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "syl.mm"
include "eqid.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "opabbidv.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "3eqtr4g.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "jca.mm"

theorem f1ocnvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cW: class W
  let cX: class X
  assume f1od.1: |- F = ( x e. A |-> C )
  assume f1od.2: |- ( ( ph /\ x e. A ) -> C e. W )
  assume f1od.3: |- ( ( ph /\ y e. B ) -> D e. X )
  assume f1od.4: |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) )

  proof
    wph
    cA
    cB
    cF
    wf1o
    #
    cF
    ccnv
    #
    vy
    cB
    cD
    cmpt
    #
    wceq
    wph
    cF
    cA
    wfn
    #
    @1
    cB
    wfn
    #
    @0
    wph
    cC
    cW
    wcel
    #
    vx
    cA
    wral
    @3
    wph
    @5
    vx
    cA
    f1od.2
    ralrimiva
    vx
    cA
    cC
    cF
    cW
    f1od.1
    fnmpt
    syl
    wph
    @4
    @2
    cB
    wfn
    #
    wph
    cD
    cX
    wcel
    #
    vy
    cB
    wral
    @6
    wph
    @7
    vy
    cB
    f1od.3
    ralrimiva
    vy
    cB
    cD
    @2
    cX
    @2
    eqid
    fnmpt
    syl
    wph
    cB
    @1
    @2
    wph
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cC
    wceq
    wa
    #
    vy
    vx
    copab
    #
    @9
    cB
    wcel
    @8
    cD
    wceq
    wa
    #
    vy
    vx
    copab
    @1
    @2
    wph
    @10
    @12
    vy
    vx
    f1od.4
    opabbidv
    @1
    @10
    vx
    vy
    copab
    #
    ccnv
    @11
    cF
    @13
    cF
    vx
    cA
    cC
    cmpt
    @13
    f1od.1
    vx
    vy
    cA
    cC
    df-mpt
    eqtri
    cnveqi
    @10
    vx
    vy
    cnvopab
    eqtri
    vy
    vx
    cB
    cD
    df-mpt
    3eqtr4g
    #
    fneq1d
    mpbird
    cA
    cB
    cF
    dff1o4
    sylanbrc
    @14
    jca
end
