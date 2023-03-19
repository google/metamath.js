include "chomf.mm"
include "cfv.mm"
include "ctpos.mm"
include "coppc.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "cbs.mm"
include "cxp.mm"
include "wfn.mm"
include "eqid.mm"
include "homffn.mm"
include "fnrel.mm"
include "ax-mp.mm"
include "relxp.mm"
include "fndm.mm"
include "releqi.mm"
include "mpbir.mm"
include "tpostpos2.mm"
include "mp2an.mm"
include "oppchomf.mm"
include "eqtr3i.mm"

theorem 2oppchomf
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


  assert |- ( Homf ` C ) = ( Homf ` ( oppCat ` O ) )

  proof
    cC
    chomf
    cfv
    #
    ctpos
    #
    ctpos
    #
    @0
    cO
    coppc
    cfv
    #
    chomf
    cfv
    @0
    wrel
    #
    @0
    cdm
    #
    wrel
    #
    @2
    @0
    wceq
    @0
    cC
    cbs
    cfv
    #
    @7
    cxp
    #
    wfn
    #
    @4
    @7
    cC
    @0
    @0
    eqid
    #
    @7
    eqid
    homffn
    #
    @8
    @0
    fnrel
    ax-mp
    @6
    @8
    wrel
    @7
    @7
    relxp
    @5
    @8
    @9
    @5
    @8
    wceq
    @11
    @8
    @0
    fndm
    ax-mp
    releqi
    mpbir
    @0
    tpostpos2
    mp2an
    cO
    @1
    @3
    @3
    eqid
    cC
    @0
    cO
    oppcbas.1
    @10
    oppchomf
    oppchomf
    eqtr3i
end
