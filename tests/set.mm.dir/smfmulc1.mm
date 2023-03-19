include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cin.mm"
include "csmblfn.mm"
include "cfv.mm"
include "wceq.mm"
include "inidm.mm"
include "eqcomi.mm"
include "mpteq1i.mm"
include "a1i.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "cdm.mm"
include "cuni.mm"
include "eqid.mm"
include "dmmptdf.mm"
include "eqcomd.mm"
include "smfdmss.mm"
include "eqsstrd.mm"
include "smfconst.mm"
include "smfmul.mm"
include "eqeltrd.mm"

theorem smfmulc1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let vk: setvar k
  assume smfmulc1.x: |- F/ x ph
  assume smfmulc1.s: |- ( ph -> S e. SAlg )
  assume smfmulc1.a: |- ( ph -> A e. V )
  assume smfmulc1.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfmulc1.c: |- ( ph -> C e. RR )
  assume smfmulc1.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )

  disjoint A x
  disjoint C x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> ( C x. B ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cC
    cB
    cmul
    co
    #
    cmpt
    #
    vx
    cA
    cA
    cin
    #
    @0
    cmpt
    #
    cS
    csmblfn
    cfv
    @1
    @3
    wceq
    wph
    vx
    cA
    @2
    @0
    @2
    cA
    cA
    inidm
    eqcomi
    mpteq1i
    a1i
    wph
    vx
    cA
    cC
    cA
    cB
    cS
    cV
    smfmulc1.x
    smfmulc1.s
    smfmulc1.a
    wph
    cC
    cr
    wcel
    vx
    cv
    cA
    wcel
    smfmulc1.c
    adantr
    smfmulc1.b
    wph
    vx
    cA
    cC
    cS
    vx
    cA
    cC
    cmpt
    #
    smfmulc1.x
    smfmulc1.s
    wph
    cA
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    cS
    cuni
    wph
    @6
    cA
    wph
    vx
    @5
    cA
    cB
    cr
    smfmulc1.x
    @5
    eqid
    smfmulc1.b
    dmmptdf
    eqcomd
    wph
    @6
    cS
    @5
    smfmulc1.s
    smfmulc1.m
    @6
    eqid
    smfdmss
    eqsstrd
    smfmulc1.c
    @4
    eqid
    smfconst
    smfmulc1.m
    smfmul
    eqeltrd
end
