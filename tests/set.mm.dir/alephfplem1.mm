include "c0.mm"
include "cfv.mm"
include "cale.mm"
include "crn.mm"
include "com.mm"
include "crdg.mm"
include "cres.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "omex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "aleph0.mm"
include "3eqtr4i.mm"
include "con0.mm"
include "wfn.mm"
include "alephfnon.mm"
include "0elon.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem alephfplem1
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume alephfplem.1: |- H = ( rec ( aleph , _om ) |` _om )


  assert |- ( H ` (/) ) e. ran aleph

  proof
    c0
    cH
    cfv
    #
    c0
    cale
    cfv
    #
    cale
    crn
    #
    c0
    cale
    com
    crdg
    com
    cres
    #
    cfv
    #
    com
    @0
    @1
    com
    cvv
    wcel
    @4
    com
    wceq
    omex
    com
    cvv
    cale
    fr0g
    ax-mp
    c0
    cH
    @3
    alephfplem.1
    fveq1i
    aleph0
    3eqtr4i
    cale
    con0
    wfn
    c0
    con0
    wcel
    @1
    @2
    wcel
    alephfnon
    0elon
    con0
    c0
    cale
    fnfvelrn
    mp2an
    eqeltri
end
