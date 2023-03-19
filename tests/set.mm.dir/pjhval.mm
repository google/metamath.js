include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "pjhfval.mm"
include "fveq1d.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem pjhval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H
  let vh: setvar h
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H h
  disjoint x z
  disjoint y z
  disjoint H z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` H ) ` A ) = ( iota_ x e. H E. y e. ( _|_ ` H ) A = ( x +h y ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    cA
    cH
    cpjh
    cfv
    #
    cfv
    cA
    vz
    chil
    vz
    cv
    #
    vx
    cv
    vy
    cv
    cva
    co
    #
    wceq
    #
    vy
    cH
    cort
    cfv
    #
    wrex
    #
    vx
    cH
    crio
    #
    cmpt
    #
    cfv
    cA
    @3
    wceq
    #
    vy
    @5
    wrex
    #
    vx
    cH
    crio
    #
    @0
    cA
    @1
    @8
    vz
    vy
    vx
    cH
    pjhfval
    fveq1d
    vz
    cA
    @7
    @11
    chil
    @8
    @2
    cA
    wceq
    #
    @6
    @10
    vx
    cH
    @12
    @4
    @9
    vy
    @5
    @2
    cA
    @3
    eqeq1
    rexbidv
    riotabidv
    @8
    eqid
    @10
    vx
    cH
    riotaex
    fvmpt
    sylan9eq
end
