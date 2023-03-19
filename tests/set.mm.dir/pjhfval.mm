include "chil.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cch.mm"
include "cpjh.mm"
include "id.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "riotaeqbidv.mm"
include "mpteq2dv.mm"
include "df-pjh.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem pjhfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let vh: setvar h
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint H x
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H h
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( H e. CH -> ( projh ` H ) = ( x e. ~H |-> ( iota_ z e. H E. y e. ( _|_ ` H ) x = ( z +h y ) ) ) )

  proof
    vh
    cH
    vx
    chil
    vx
    cv
    vz
    cv
    vy
    cv
    cva
    co
    wceq
    #
    vy
    vh
    cv
    #
    cort
    cfv
    #
    wrex
    #
    vz
    @1
    crio
    #
    cmpt
    vx
    chil
    @0
    vy
    cH
    cort
    cfv
    #
    wrex
    #
    vz
    cH
    crio
    #
    cmpt
    cch
    cpjh
    @1
    cH
    wceq
    #
    vx
    chil
    @4
    @7
    @8
    @3
    @6
    vz
    @1
    cH
    @8
    id
    @8
    @0
    vy
    @2
    @5
    @1
    cH
    cort
    fveq2
    rexeqdv
    riotaeqbidv
    mpteq2dv
    vx
    vy
    vz
    vh
    df-pjh
    vx
    chil
    @7
    ax-hilex
    mptex
    fvmpt
end
