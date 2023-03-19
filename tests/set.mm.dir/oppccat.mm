include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "wceq.mm"
include "oppccatid.mm"
include "simpld.mm"

theorem oppccat
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


  assert |- ( C e. Cat -> O e. Cat )

  proof
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    cO
    ccid
    cfv
    cC
    ccid
    cfv
    wceq
    cC
    cO
    oppcbas.1
    oppccatid
    simpld
end
