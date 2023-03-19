include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "cvv.mm"
include "isrnsiga.mm"
include "simprbi.mm"
include "3simpa.mm"
include "adantl.mm"
include "eximi.mm"
include "weq.mm"
include "difeq2.mm"
include "difid.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "exlimiv.mm"
include "3syl.mm"

theorem 0elsiga
  let cS: class S
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x


  assert |- ( S e. U. ran sigAlgebra -> (/) e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cS
    vo
    cv
    #
    cpw
    wss
    #
    @1
    cS
    wcel
    #
    @1
    vx
    cv
    #
    cdif
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @4
    com
    cdom
    wbr
    @4
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    wral
    #
    w3a
    #
    wa
    #
    vo
    wex
    #
    @3
    @7
    wa
    #
    vo
    wex
    c0
    cS
    wcel
    #
    @0
    cS
    cvv
    wcel
    @11
    vx
    cS
    vo
    isrnsiga
    simprbi
    @10
    @12
    vo
    @9
    @12
    @2
    @3
    @7
    @8
    3simpa
    adantl
    eximi
    @12
    @13
    vo
    @6
    @13
    vx
    @1
    cS
    vx
    vo
    weq
    #
    @5
    c0
    cS
    @14
    @5
    @1
    @1
    cdif
    c0
    @4
    @1
    @1
    difeq2
    @1
    difid
    syl6eq
    eleq1d
    rspcva
    exlimiv
    3syl
end
