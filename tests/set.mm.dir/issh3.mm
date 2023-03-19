include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "issh2.mm"
include "anass.mm"
include "baib.mm"
include "syl5bb.mm"

theorem issh3
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( H C_ ~H -> ( H e. SH <-> ( 0h e. H /\ ( A. x e. H A. y e. H ( x +h y ) e. H /\ A. x e. CC A. y e. H ( x .h y ) e. H ) ) ) )

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    #
    c0v
    cH
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    cH
    wcel
    vy
    cH
    wral
    vx
    cH
    wral
    @2
    @3
    csm
    co
    cH
    wcel
    vy
    cH
    wral
    vx
    cc
    wral
    wa
    #
    wa
    #
    @0
    @1
    @4
    wa
    #
    vx
    vy
    cH
    issh2
    @5
    @0
    @6
    @0
    @1
    @4
    anass
    baib
    syl5bb
end
