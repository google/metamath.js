include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cif.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "cpr.mm"
include "wa.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "df-2.mm"
include "oveq2i.mm"
include "preq2i.mm"
include "3eqtr4i.mm"
include "raleqi.mm"
include "1ex.mm"
include "2ex.mm"
include "fveq2.mm"
include "iftrue.mm"
include "eqeq12d.mm"
include "wne.mm"
include "1ne2.mm"
include "necomi.mm"
include "pm13.181.mm"
include "mpan2.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "ralpr.mm"
include "bitri.mm"

theorem fzprval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( A. x e. ( 1 ... 2 ) ( F ` x ) = if ( x = 1 , A , B ) <-> ( ( F ` 1 ) = A /\ ( F ` 2 ) = B ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    @0
    c1
    wceq
    #
    cA
    cB
    cif
    #
    wceq
    #
    vx
    c1
    c2
    cfz
    co
    #
    wral
    @4
    vx
    c1
    c2
    cpr
    #
    wral
    c1
    cF
    cfv
    #
    cA
    wceq
    #
    c2
    cF
    cfv
    #
    cB
    wceq
    #
    wa
    @4
    vx
    @5
    @6
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    c1
    @11
    cpr
    #
    @5
    @6
    c1
    cz
    wcel
    @12
    @13
    wceq
    1z
    c1
    fzpr
    ax-mp
    c2
    @11
    c1
    cfz
    df-2
    oveq2i
    c2
    @11
    c1
    df-2
    preq2i
    3eqtr4i
    raleqi
    @4
    @8
    @10
    vx
    c1
    c2
    1ex
    2ex
    @2
    @1
    @7
    @3
    cA
    @0
    c1
    cF
    fveq2
    @2
    cA
    cB
    iftrue
    eqeq12d
    @0
    c2
    wceq
    #
    @1
    @9
    @3
    cB
    @0
    c2
    cF
    fveq2
    @14
    @2
    cA
    cB
    @14
    @0
    c1
    @14
    c2
    c1
    wne
    @0
    c1
    wne
    c1
    c2
    1ne2
    necomi
    @0
    c2
    c1
    pm13.181
    mpan2
    neneqd
    iffalsed
    eqeq12d
    ralpr
    bitri
end
