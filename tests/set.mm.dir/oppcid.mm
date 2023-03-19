include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "wceq.mm"
include "oppccatid.mm"
include "simprd.mm"
include "syl6eqr.mm"

theorem oppcid
  let cB: class B
  let cC: class C
  let cO: class O
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppcbas.1: |- O = ( oppCat ` C )
  assume oppcid.2: |- B = ( Id ` C )


  assert |- ( C e. Cat -> ( Id ` O ) = B )

  proof
    cC
    ccat
    wcel
    #
    cO
    ccid
    cfv
    #
    cC
    ccid
    cfv
    #
    cB
    @0
    cO
    ccat
    wcel
    @1
    @2
    wceq
    cC
    cO
    oppcbas.1
    oppccatid
    simprd
    oppcid.2
    syl6eqr
end
