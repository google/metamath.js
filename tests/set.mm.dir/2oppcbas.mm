include "coppc.mm"
include "cfv.mm"
include "eqid.mm"
include "oppcbas.mm"

theorem 2oppcbas
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
  assume 2oppcco.2: |- B = ( Base ` C )


  assert |- B = ( Base ` ( oppCat ` O ) )

  proof
    cB
    cO
    cO
    coppc
    cfv
    #
    @0
    eqid
    cB
    cC
    cO
    oppcbas.1
    2oppcco.2
    oppcbas
    oppcbas
end
