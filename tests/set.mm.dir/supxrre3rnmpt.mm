include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "supxrre3.mm"
include "syl2anc.mm"
include "rnmptbd.mm"
include "bitr4d.mm"

theorem supxrre3rnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume supxrre3rnmpt.x: |- F/ x ph
  assume supxrre3rnmpt.a: |- ( ph -> A =/= (/) )
  assume supxrre3rnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ph -> ( sup ( ran ( x e. A |-> B ) , RR* , < ) e. RR <-> E. y e. RR A. x e. A B <_ y ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    cr
    wcel
    #
    vz
    cv
    vy
    cv
    #
    cle
    wbr
    vz
    @1
    wral
    vy
    cr
    wrex
    #
    cB
    @3
    cle
    wbr
    vx
    cA
    wral
    vy
    cr
    wrex
    wph
    @1
    cr
    wss
    @1
    c0
    wne
    @2
    @4
    wb
    wph
    vx
    cA
    cB
    cr
    @0
    supxrre3rnmpt.x
    @0
    eqid
    #
    supxrre3rnmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    supxrre3rnmpt.x
    supxrre3rnmpt.b
    @5
    supxrre3rnmpt.a
    rnmptn0
    vy
    vz
    @1
    supxrre3
    syl2anc
    wph
    vx
    vy
    vz
    cA
    cB
    cr
    supxrre3rnmpt.x
    supxrre3rnmpt.b
    rnmptbd
    bitr4d
end
