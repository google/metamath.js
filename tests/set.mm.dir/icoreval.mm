include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "crab.mm"
include "ovres.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eqid.mm"
include "icorempt2.mm"
include "reex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "eqtr3d.mm"

theorem icoreval
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y

  disjoint A z
  disjoint B z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A [,) B ) = { z e. RR | ( A <_ z /\ z < B ) } )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    cA
    cB
    cico
    cr
    cr
    cxp
    cres
    #
    co
    cA
    cB
    cico
    co
    cA
    vz
    cv
    #
    cle
    wbr
    #
    @1
    cB
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    #
    cA
    cB
    cr
    cr
    cico
    ovres
    vx
    vy
    cA
    cB
    cr
    cr
    vx
    cv
    #
    @1
    cle
    wbr
    #
    @1
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    @5
    @0
    @2
    @9
    wa
    #
    vz
    cr
    crab
    @6
    cA
    wceq
    #
    @10
    @11
    vz
    cr
    @12
    @7
    @2
    @9
    @6
    cA
    @1
    cle
    breq1
    anbi1d
    rabbidv
    @8
    cB
    wceq
    #
    @11
    @4
    vz
    cr
    @13
    @9
    @3
    @2
    @8
    cB
    @1
    clt
    breq2
    anbi2d
    rabbidv
    vx
    vy
    vz
    @0
    @0
    eqid
    icorempt2
    @4
    vz
    cr
    reex
    rabex
    ovmpt2
    eqtr3d
end
