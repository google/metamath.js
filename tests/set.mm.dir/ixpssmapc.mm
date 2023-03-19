include "cixp.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "ssexd.mm"
include "ixpssmap2g.mm"
include "syl.mm"
include "mapss.mm"
include "syl2anc.mm"
include "sstrd.mm"

theorem ixpssmapc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume ixpssmapc.x: |- F/ x ph
  assume ixpssmapc.c: |- ( ph -> C e. V )
  assume ixpssmapc.b: |- ( ( ph /\ x e. A ) -> B C_ C )

  disjoint A x
  disjoint C x
  assert |- ( ph -> X_ x e. A B C_ ( C ^m A ) )

  proof
    wph
    vx
    cA
    cB
    cixp
    #
    vx
    cA
    cB
    ciun
    #
    cA
    cmap
    co
    #
    cC
    cA
    cmap
    co
    #
    wph
    @1
    cvv
    wcel
    @0
    @2
    wss
    wph
    @1
    cC
    cV
    ixpssmapc.c
    wph
    cB
    cC
    wss
    #
    vx
    cA
    wral
    @1
    cC
    wss
    #
    wph
    @4
    vx
    cA
    ixpssmapc.x
    wph
    vx
    cv
    cA
    wcel
    @4
    ixpssmapc.b
    ex
    ralrimi
    vx
    cA
    cB
    cC
    iunss
    sylibr
    #
    ssexd
    vx
    cA
    cB
    cvv
    ixpssmap2g
    syl
    wph
    cC
    cV
    wcel
    @5
    @2
    @3
    wss
    ixpssmapc.c
    @6
    @1
    cC
    cA
    cV
    mapss
    syl2anc
    sstrd
end
