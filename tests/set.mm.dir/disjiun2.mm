include "ciun.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "iunxsng.mm"
include "syl.mm"
include "ineq2d.mm"
include "wdisj.mm"
include "wss.mm"
include "eldifi.mm"
include "snssi.mm"
include "3syl.mm"
include "wn.mm"
include "eldifbd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjiun.mm"
include "syl13anc.mm"
include "eqtr3d.mm"

theorem disjiun2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume disjiun2.1: |- ( ph -> Disj_ x e. A B )
  assume disjiun2.2: |- ( ph -> C C_ A )
  assume disjiun2.3: |- ( ph -> D e. ( A \ C ) )
  assume disjiun2.4: |- ( x = D -> B = E )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint E x
  assert |- ( ph -> ( U_ x e. C B i^i E ) = (/) )

  proof
    wph
    vx
    cC
    cB
    ciun
    #
    vx
    cD
    csn
    #
    cB
    ciun
    #
    cin
    #
    @0
    cE
    cin
    c0
    wph
    @2
    cE
    @0
    wph
    cD
    cA
    cC
    cdif
    #
    wcel
    #
    @2
    cE
    wceq
    disjiun2.3
    vx
    cD
    cB
    cE
    @4
    disjiun2.4
    iunxsng
    syl
    ineq2d
    wph
    vx
    cA
    cB
    wdisj
    cC
    cA
    wss
    @1
    cA
    wss
    #
    cC
    @1
    cin
    c0
    wceq
    #
    @3
    c0
    wceq
    disjiun2.1
    disjiun2.2
    wph
    @5
    cD
    cA
    wcel
    @6
    disjiun2.3
    cD
    cA
    cC
    eldifi
    cD
    cA
    snssi
    3syl
    wph
    cD
    cC
    wcel
    wn
    @7
    wph
    cD
    cA
    cC
    disjiun2.3
    eldifbd
    cC
    cD
    disjsn
    sylibr
    vx
    cA
    cB
    cC
    @1
    disjiun
    syl13anc
    eqtr3d
end
