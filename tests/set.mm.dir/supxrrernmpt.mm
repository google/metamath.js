include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "rnmptbdd.mm"
include "supxrre.mm"
include "syl3anc.mm"

theorem supxrrernmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume supxrrernmpt.x: |- F/ x ph
  assume supxrrernmpt.a: |- ( ph -> A =/= (/) )
  assume supxrrernmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume supxrrernmpt.y: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ph -> sup ( ran ( x e. A |-> B ) , RR* , < ) = sup ( ran ( x e. A |-> B ) , RR , < ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cr
    wss
    @1
    c0
    wne
    vz
    cv
    vy
    cv
    cle
    wbr
    vz
    @1
    wral
    vy
    cr
    wrex
    @1
    cxr
    clt
    csup
    @1
    cr
    clt
    csup
    wceq
    wph
    vx
    cA
    cB
    cr
    @0
    supxrrernmpt.x
    @0
    eqid
    #
    supxrrernmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    supxrrernmpt.x
    supxrrernmpt.b
    @2
    supxrrernmpt.a
    rnmptn0
    wph
    vx
    vy
    vz
    cA
    cB
    supxrrernmpt.x
    supxrrernmpt.y
    rnmptbdd
    vy
    vz
    @1
    supxrre
    syl3anc
end
