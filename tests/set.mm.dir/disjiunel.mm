include "wdisj.mm"
include "ciun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "wss.mm"
include "eldifad.mm"
include "snssd.mm"
include "unssd.mm"
include "disjss1.mm"
include "sylc.mm"
include "wcel.mm"
include "wn.mm"
include "wb.mm"
include "eldifbd.mm"
include "disjunsn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"

theorem disjiunel
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cY: class Y
  assume disjiunel.1: |- ( ph -> Disj_ x e. A B )
  assume disjiunel.2: |- ( x = Y -> B = D )
  assume disjiunel.3: |- ( ph -> E C_ A )
  assume disjiunel.4: |- ( ph -> Y e. ( A \ E ) )

  disjoint A x
  disjoint D x
  disjoint E x
  disjoint Y x
  assert |- ( ph -> ( U_ x e. E B i^i D ) = (/) )

  proof
    wph
    vx
    cE
    cB
    wdisj
    #
    vx
    cE
    cB
    ciun
    cD
    cin
    c0
    wceq
    #
    wph
    vx
    cE
    cY
    csn
    #
    cun
    #
    cB
    wdisj
    #
    @0
    @1
    wa
    #
    wph
    @3
    cA
    wss
    vx
    cA
    cB
    wdisj
    @4
    wph
    cE
    @2
    cA
    disjiunel.3
    wph
    cY
    cA
    wph
    cY
    cA
    cE
    disjiunel.4
    eldifad
    #
    snssd
    unssd
    disjiunel.1
    vx
    @3
    cA
    cB
    disjss1
    sylc
    wph
    cY
    cA
    wcel
    cY
    cE
    wcel
    wn
    @4
    @5
    wb
    @6
    wph
    cY
    cA
    cE
    disjiunel.4
    eldifbd
    vx
    cE
    cB
    cD
    cY
    cA
    disjiunel.2
    disjunsn
    syl2anc
    mpbid
    simprd
end
