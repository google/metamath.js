include "wor.mm"
include "c0.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "id.mm"
include "supval2.mm"
include "wb.mm"
include "ral0.mm"
include "biantrur.mm"
include "rex0.mm"
include "imnot.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "a1i.mm"
include "riotabidv.mm"
include "eqtrd.mm"

theorem sup0riota
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint R z
  assert |- ( R Or A -> sup ( (/) , A , R ) = ( iota_ x e. A A. y e. A -. y R x ) )

  proof
    cA
    cR
    wor
    #
    c0
    cA
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    #
    vy
    c0
    wral
    #
    @2
    @1
    cR
    wbr
    #
    @2
    vz
    cv
    cR
    wbr
    #
    vz
    c0
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crio
    @5
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    crio
    @0
    vx
    vy
    vz
    cA
    c0
    cR
    @0
    id
    supval2
    @0
    @10
    @12
    vx
    cA
    @10
    @12
    wb
    @0
    @10
    @9
    @12
    @4
    @9
    @3
    vy
    ral0
    biantrur
    @8
    @11
    vy
    cA
    @7
    wn
    @8
    @11
    wb
    @6
    vz
    rex0
    @5
    @7
    imnot
    ax-mp
    ralbii
    bitr3i
    a1i
    riotabidv
    eqtrd
end
