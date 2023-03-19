include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cuni.mm"
include "cun.mm"
include "cv.mm"
include "ciun.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "iunconst.mm"
include "sylbir.mm"
include "iun0.mm"
include "id.mm"
include "iuneq2d.mm"
include "3eqtr4a.mm"
include "ja.mm"
include "eqcomd.mm"
include "uneq1d.mm"
include "uniiun.mm"
include "uneq2i.mm"
include "iunun.mm"
include "3eqtr4g.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "uneq2d.mm"
include "un0.mm"
include "iuneq1.mm"
include "0iun.mm"
include "eqeq12d.mm"
include "biimpcd.mm"
include "impbii.mm"

theorem iununi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( B = (/) -> A = (/) ) <-> ( A u. U. B ) = U_ x e. B ( A u. x ) )

  proof
    cB
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    wi
    #
    cA
    cB
    cuni
    #
    cun
    #
    vx
    cB
    cA
    vx
    cv
    #
    cun
    #
    ciun
    #
    wceq
    #
    @2
    cA
    vx
    cB
    @5
    ciun
    #
    cun
    vx
    cB
    cA
    ciun
    #
    @9
    cun
    @4
    @7
    @2
    cA
    @10
    @9
    @2
    @10
    cA
    @0
    @1
    @10
    cA
    wceq
    #
    @0
    wn
    cB
    c0
    wne
    @11
    cB
    c0
    df-ne
    vx
    cB
    cA
    iunconst
    sylbir
    @1
    vx
    cB
    c0
    ciun
    c0
    @10
    cA
    vx
    cB
    iun0
    @1
    vx
    cB
    cA
    c0
    @1
    id
    #
    iuneq2d
    @12
    3eqtr4a
    ja
    eqcomd
    uneq1d
    @3
    @9
    cA
    vx
    cB
    uniiun
    uneq2i
    vx
    cB
    cA
    @5
    iunun
    3eqtr4g
    @0
    @8
    @1
    @0
    @4
    cA
    @7
    c0
    @0
    @4
    cA
    c0
    cun
    cA
    @0
    @3
    c0
    cA
    @0
    @3
    c0
    cuni
    c0
    cB
    c0
    unieq
    uni0
    syl6eq
    uneq2d
    cA
    un0
    syl6eq
    @0
    @7
    vx
    c0
    @6
    ciun
    c0
    vx
    cB
    c0
    @6
    iuneq1
    vx
    @6
    0iun
    syl6eq
    eqeq12d
    biimpcd
    impbii
end
