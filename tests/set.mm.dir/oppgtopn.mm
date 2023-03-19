include "ctopn.mm"
include "cfv.mm"
include "cts.mm"
include "cbs.mm"
include "crest.mm"
include "co.mm"
include "eqid.mm"
include "topnval.mm"
include "oppgbas.mm"
include "oppgtset.mm"
include "3eqtr2i.mm"

theorem oppgtopn
  let cR: class R
  let cJ: class J
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppgtopn.2: |- J = ( TopOpen ` R )


  assert |- J = ( TopOpen ` O )

  proof
    cJ
    cR
    ctopn
    cfv
    cR
    cts
    cfv
    #
    cR
    cbs
    cfv
    #
    crest
    co
    cO
    ctopn
    cfv
    oppgtopn.2
    @1
    @0
    cR
    @1
    eqid
    #
    @0
    eqid
    #
    topnval
    @1
    @0
    cO
    @1
    cR
    cO
    oppgbas.1
    @2
    oppgbas
    cR
    @0
    cO
    oppgbas.1
    @3
    oppgtset
    topnval
    3eqtr2i
end
