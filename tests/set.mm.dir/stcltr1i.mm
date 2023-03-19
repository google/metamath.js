include "cst.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "cch.mm"
include "wral.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi1d.mm"
include "sseq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "sseq2.mm"
include "rspc2v.mm"
include "mp2an.mm"
include "simplbiim.mm"

theorem stcltr1i
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  assume stcltr1.1: |- ( ph <-> ( S e. States /\ A. x e. CH A. y e. CH ( ( ( S ` x ) = 1 -> ( S ` y ) = 1 ) -> x C_ y ) ) )
  assume stcltr1.2: |- A e. CH
  assume stcltr1.3: |- B e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( ( ( S ` A ) = 1 -> ( S ` B ) = 1 ) -> A C_ B ) )

  proof
    wph
    cS
    cst
    wcel
    vx
    cv
    #
    cS
    cfv
    #
    c1
    wceq
    #
    vy
    cv
    #
    cS
    cfv
    #
    c1
    wceq
    #
    wi
    #
    @0
    @3
    wss
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    cA
    cS
    cfv
    #
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    c1
    wceq
    #
    wi
    #
    cA
    cB
    wss
    #
    wi
    #
    stcltr1.1
    cA
    cch
    wcel
    cB
    cch
    wcel
    @9
    @16
    wi
    stcltr1.2
    stcltr1.3
    @8
    @16
    @11
    @5
    wi
    #
    cA
    @3
    wss
    #
    wi
    vx
    vy
    cA
    cB
    cch
    cch
    @0
    cA
    wceq
    #
    @6
    @17
    @7
    @18
    @19
    @2
    @11
    @5
    @19
    @1
    @10
    c1
    @0
    cA
    cS
    fveq2
    eqeq1d
    imbi1d
    @0
    cA
    @3
    sseq1
    imbi12d
    @3
    cB
    wceq
    #
    @17
    @14
    @18
    @15
    @20
    @5
    @13
    @11
    @20
    @4
    @12
    c1
    @3
    cB
    cS
    fveq2
    eqeq1d
    imbi2d
    @3
    cB
    cA
    sseq2
    imbi12d
    rspc2v
    mp2an
    simplbiim
end
