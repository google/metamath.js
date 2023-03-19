include "com.mm"
include "cale.mm"
include "crn.mm"
include "cun.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wrex.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "wfn.mm"
include "wral.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "alephfplem3.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "ssun2.mm"
include "fss.mm"
include "mp2an.mm"
include "c0.mm"
include "peano1.mm"
include "alephfplem1.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "cvv.mm"
include "wa.mm"
include "wi.mm"
include "omex.mm"
include "cardinfima.mm"
include "ax-mp.mm"

theorem alephfplem4
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume alephfplem.1: |- H = ( rec ( aleph , _om ) |` _om )


  assert |- U. ( H " _om ) e. ran aleph

  proof
    com
    com
    cale
    crn
    #
    cun
    #
    cH
    wf
    #
    vz
    cv
    #
    cH
    cfv
    #
    @0
    wcel
    #
    vz
    com
    wrex
    #
    cH
    com
    cima
    cuni
    @0
    wcel
    #
    com
    @0
    cH
    wf
    #
    @0
    @1
    wss
    @2
    @8
    cH
    com
    wfn
    #
    @5
    vz
    com
    wral
    @9
    cale
    com
    crdg
    com
    cres
    #
    com
    wfn
    com
    cale
    frfnom
    com
    cH
    @10
    alephfplem.1
    fneq1i
    mpbir
    @5
    vz
    com
    vz
    cH
    alephfplem.1
    alephfplem3
    rgen
    vz
    com
    @0
    cH
    ffnfv
    mpbir2an
    @0
    com
    ssun2
    com
    @0
    @1
    cH
    fss
    mp2an
    c0
    com
    wcel
    c0
    cH
    cfv
    #
    @0
    wcel
    #
    @6
    peano1
    cH
    alephfplem.1
    alephfplem1
    @5
    @12
    vz
    c0
    com
    @3
    c0
    wceq
    @4
    @11
    @0
    @3
    c0
    cH
    fveq2
    eleq1d
    rspcev
    mp2an
    com
    cvv
    wcel
    @2
    @6
    wa
    @7
    wi
    omex
    vz
    com
    cvv
    cH
    cardinfima
    ax-mp
    mp2an
end
