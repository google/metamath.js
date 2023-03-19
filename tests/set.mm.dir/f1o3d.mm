include "wf1o.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "wi.mm"
include "eleq1a.mm"
include "impr.mm"
include "biimpar.mm"
include "exp42.mm"
include "com34.mm"
include "imp32.mm"
include "jcai.mm"
include "biimpa.mm"
include "com23.mm"
include "impbida.mm"
include "opabbidv.mm"
include "df-mpt.mm"
include "syl6eq.mm"
include "cnveqd.mm"
include "cnvopab.mm"
include "a1i.mm"
include "3eqtr4d.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "jca.mm"

theorem f1o3d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume f1o3d.1: |- ( ph -> F = ( x e. A |-> C ) )
  assume f1o3d.2: |- ( ( ph /\ x e. A ) -> C e. B )
  assume f1o3d.3: |- ( ( ph /\ y e. B ) -> D e. A )
  assume f1o3d.4: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) )

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
    @3
    vx
    cA
    cC
    cmpt
    #
    cA
    wfn
    #
    wph
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    @6
    wph
    @7
    vx
    cA
    f1o3d.2
    ralrimiva
    vx
    cA
    cC
    @5
    cB
    @5
    eqid
    fnmpt
    syl
    wph
    cA
    cF
    @5
    f1o3d.1
    fneq1d
    mpbird
    wph
    @4
    @2
    cB
    wfn
    #
    wph
    cD
    cA
    wcel
    #
    vy
    cB
    wral
    @8
    wph
    @9
    vy
    cB
    f1o3d.3
    ralrimiva
    vy
    cB
    cD
    @2
    cA
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
    #
    vy
    cv
    #
    cC
    wceq
    #
    wa
    #
    vy
    vx
    copab
    #
    @12
    cB
    wcel
    #
    @10
    cD
    wceq
    #
    wa
    #
    vy
    vx
    copab
    #
    @1
    @2
    wph
    @14
    @18
    vy
    vx
    wph
    @14
    @18
    wph
    @14
    wa
    @16
    @17
    wph
    @11
    @13
    @16
    wph
    @11
    wa
    @7
    @13
    @16
    wi
    f1o3d.2
    cC
    cB
    @12
    eleq1a
    syl
    impr
    wph
    @11
    @13
    @16
    @17
    wi
    wph
    @11
    @16
    @13
    @17
    wph
    @11
    @16
    @13
    @17
    wph
    @11
    @16
    wa
    wa
    #
    @17
    @13
    f1o3d.4
    biimpar
    exp42
    com34
    imp32
    jcai
    wph
    @18
    wa
    @11
    @13
    wph
    @16
    @17
    @11
    wph
    @16
    wa
    @9
    @17
    @11
    wi
    f1o3d.3
    cD
    cA
    @10
    eleq1a
    syl
    impr
    wph
    @16
    @17
    @11
    @13
    wi
    wph
    @16
    @11
    @17
    @13
    wph
    @11
    @16
    @17
    @13
    wi
    wph
    @11
    @16
    @17
    @13
    @20
    @17
    @13
    f1o3d.4
    biimpa
    exp42
    com23
    com34
    imp32
    jcai
    impbida
    opabbidv
    wph
    @1
    @14
    vx
    vy
    copab
    #
    ccnv
    @15
    wph
    cF
    @21
    wph
    cF
    @5
    @21
    f1o3d.1
    vx
    vy
    cA
    cC
    df-mpt
    syl6eq
    cnveqd
    @14
    vx
    vy
    cnvopab
    syl6eq
    @2
    @19
    wceq
    wph
    vy
    vx
    cB
    cD
    df-mpt
    a1i
    3eqtr4d
    #
    fneq1d
    mpbird
    cA
    cB
    cF
    dff1o4
    sylanbrc
    @22
    jca
end
