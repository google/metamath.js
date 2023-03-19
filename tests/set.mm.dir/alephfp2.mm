include "cale.mm"
include "com.mm"
include "crdg.mm"
include "cres.mm"
include "cima.mm"
include "cuni.mm"
include "con0.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "crn.mm"
include "alephsson.mm"
include "eqid.mm"
include "alephfplem4.mm"
include "sselii.mm"
include "alephfp.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcev.mm"
include "mp2an.mm"

theorem alephfp2
  let vx: setvar x


  assert |- E. x e. On ( aleph ` x ) = x

  proof
    cale
    com
    crdg
    com
    cres
    #
    com
    cima
    cuni
    #
    con0
    wcel
    @1
    cale
    cfv
    #
    @1
    wceq
    #
    vx
    cv
    #
    cale
    cfv
    #
    @4
    wceq
    #
    vx
    con0
    wrex
    cale
    crn
    con0
    @1
    alephsson
    @0
    @0
    eqid
    #
    alephfplem4
    sselii
    @0
    @7
    alephfp
    @6
    @3
    vx
    @1
    con0
    @4
    @1
    wceq
    #
    @5
    @2
    @4
    @1
    @4
    @1
    cale
    fveq2
    @8
    id
    eqeq12d
    rspcev
    mp2an
end
