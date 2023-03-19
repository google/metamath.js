include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "rnmptfi.mm"
include "syl.mm"
include "rnmptn0.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"

theorem fisupclrnmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume fisupclrnmpt.x: |- F/ x ph
  assume fisupclrnmpt.r: |- ( ph -> R Or A )
  assume fisupclrnmpt.b: |- ( ph -> B e. Fin )
  assume fisupclrnmpt.n: |- ( ph -> B =/= (/) )
  assume fisupclrnmpt.c: |- ( ( ph /\ x e. B ) -> C e. A )

  disjoint A x
  disjoint B x
  assert |- ( ph -> sup ( ran ( x e. B |-> C ) , A , R ) e. A )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    crn
    #
    cA
    @1
    cA
    cR
    csup
    #
    wph
    vx
    cB
    cC
    cA
    @0
    fisupclrnmpt.x
    @0
    eqid
    #
    fisupclrnmpt.c
    rnmptssd
    #
    wph
    cA
    cR
    wor
    @1
    cfn
    wcel
    #
    @1
    c0
    wne
    @1
    cA
    wss
    @2
    @1
    wcel
    fisupclrnmpt.r
    wph
    cB
    cfn
    wcel
    @5
    fisupclrnmpt.b
    vx
    @0
    cB
    cC
    @3
    rnmptfi
    syl
    wph
    vx
    cB
    cC
    @0
    cA
    fisupclrnmpt.x
    fisupclrnmpt.c
    @3
    fisupclrnmpt.n
    rnmptn0
    @4
    cA
    @1
    cR
    fisupcl
    syl13anc
    sseldd
end
