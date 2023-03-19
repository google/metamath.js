include "cmpt.mm"
include "nfmpt1.mm"
include "cr.mm"
include "eqid.mm"
include "fmptdf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "eqidd.mm"
include "fvmpt2d.mm"
include "breq1d.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabbi.mm"
include "sylib.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "issmfdf.mm"

theorem issmfdmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vk: setvar k
  assume issmfdmpt.x: |- F/ x ph
  assume issmfdmpt.a: |- F/ a ph
  assume issmfdmpt.s: |- ( ph -> S e. SAlg )
  assume issmfdmpt.i: |- ( ph -> A C_ U. S )
  assume issmfdmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume issmfdmpt.p: |- ( ( ph /\ a e. RR ) -> { x e. A | B < a } e. ( S |`t A ) )

  disjoint A a
  disjoint A x
  disjoint a x
  disjoint B a
  disjoint S a
  disjoint k x
  assert |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cS
    vx
    cA
    cB
    cmpt
    #
    va
    vx
    cA
    cB
    nfmpt1
    issmfdmpt.a
    issmfdmpt.s
    issmfdmpt.i
    wph
    vx
    cA
    cB
    cr
    @0
    issmfdmpt.x
    issmfdmpt.b
    @0
    eqid
    fmptdf
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    vx
    cv
    #
    @0
    cfv
    #
    @1
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cB
    @1
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cS
    cA
    crest
    co
    wph
    @6
    @8
    wceq
    #
    @2
    wph
    @5
    @7
    wb
    #
    vx
    cA
    wral
    @9
    wph
    @10
    vx
    cA
    issmfdmpt.x
    wph
    @3
    cA
    wcel
    #
    @10
    wph
    @11
    wa
    @4
    cB
    @1
    clt
    wph
    vx
    cA
    cB
    @0
    cr
    wph
    @0
    eqidd
    issmfdmpt.b
    fvmpt2d
    breq1d
    ex
    ralrimi
    @5
    @7
    vx
    cA
    rabbi
    sylib
    adantr
    issmfdmpt.p
    eqeltrd
    issmfdf
end
