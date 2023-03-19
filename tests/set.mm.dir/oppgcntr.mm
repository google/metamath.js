include "cbs.mm"
include "cfv.mm"
include "ccntz.mm"
include "ccntr.mm"
include "eqid.mm"
include "oppgcntz.mm"
include "cntrval.mm"
include "eqtr4i.mm"
include "oppgbas.mm"
include "3eqtr3i.mm"

theorem oppgcntr
  let cG: class G
  let cO: class O
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume oppggic.o: |- O = ( oppG ` G )
  assume oppgcntr.z: |- Z = ( Cntr ` G )


  assert |- Z = ( Cntr ` O )

  proof
    cG
    cbs
    cfv
    #
    cG
    ccntz
    cfv
    #
    cfv
    #
    @0
    cO
    ccntz
    cfv
    #
    cfv
    cZ
    cO
    ccntr
    cfv
    @0
    cG
    cO
    @1
    oppggic.o
    @1
    eqid
    #
    oppgcntz
    @2
    cG
    ccntr
    cfv
    cZ
    @0
    cG
    @1
    @0
    eqid
    #
    @4
    cntrval
    oppgcntr.z
    eqtr4i
    @0
    cO
    @3
    @0
    cG
    cO
    oppggic.o
    @5
    oppgbas
    @3
    eqid
    cntrval
    3eqtr3i
end
