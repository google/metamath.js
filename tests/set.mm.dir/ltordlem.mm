include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "chvarv.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem ltordlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cM: class M
  let cN: class N
  assume ltord.1: |- ( x = y -> A = B )
  assume ltord.2: |- ( x = C -> A = M )
  assume ltord.3: |- ( x = D -> A = N )
  assume ltord.4: |- S C_ RR
  assume ltord.5: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume ltord.6: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x < y -> A < B ) )

  disjoint B x
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  assert |- ( ( ph /\ ( C e. S /\ D e. S ) ) -> ( C < D -> M < N ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    vx
    cS
    wral
    cC
    cS
    wcel
    cD
    cS
    wcel
    wa
    cC
    cD
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
    #
    wi
    #
    wph
    @4
    vx
    vy
    cS
    cS
    ltord.6
    ralrimivva
    @4
    @7
    cC
    @1
    clt
    wbr
    #
    cM
    cB
    clt
    wbr
    #
    wi
    vx
    vy
    cC
    cD
    cS
    cS
    @0
    cC
    wceq
    #
    @2
    @8
    @3
    @9
    @0
    cC
    @1
    clt
    breq1
    @10
    cA
    cM
    cB
    clt
    ltord.2
    breq1d
    imbi12d
    @1
    cD
    wceq
    #
    @8
    @5
    @9
    @6
    @1
    cD
    cC
    clt
    breq2
    @11
    cB
    cN
    cM
    clt
    @0
    cD
    wceq
    #
    cA
    cN
    wceq
    #
    wi
    @11
    cB
    cN
    wceq
    #
    wi
    vx
    vy
    @0
    @1
    wceq
    #
    @12
    @11
    @13
    @14
    @0
    @1
    cD
    eqeq1
    @15
    cA
    cB
    cN
    ltord.1
    eqeq1d
    imbi12d
    ltord.3
    chvarv
    breq2d
    imbi12d
    rspc2v
    mpan9
end
