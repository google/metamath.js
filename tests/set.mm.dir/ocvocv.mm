include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "ocvss.mm"
include "a1i.mm"
include "simpr.mm"
include "sselda.mm"
include "eqid.mm"
include "ocvi.mm"
include "ancoms.mm"
include "adantll.mm"
include "wb.mm"
include "simplll.mm"
include "adantr.mm"
include "iporthcom.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "elocv.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ocvocv
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ocvss.v: |- V = ( Base ` W )
  assume ocvss.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> S C_ ( ._|_ ` ( ._|_ ` S ) ) )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    vx
    cS
    cS
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @2
    vx
    cv
    #
    cS
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @3
    cV
    wss
    #
    @5
    cV
    wcel
    #
    @5
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    @7
    @9
    @8
    cS
    c.pe
    cV
    cW
    ocvss.v
    ocvss.o
    ocvss
    a1i
    #
    @2
    cS
    cV
    @5
    @0
    @1
    simpr
    sselda
    #
    @8
    @15
    vy
    @3
    @8
    @11
    @3
    wcel
    #
    wa
    #
    @11
    @5
    @12
    co
    @14
    wceq
    #
    @15
    @6
    @18
    @20
    @2
    @18
    @6
    @20
    @11
    @5
    cS
    @13
    @12
    c.pe
    cV
    cW
    @14
    ocvss.v
    @12
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    ocvss.o
    ocvi
    ancoms
    adantll
    @19
    @0
    @11
    cV
    wcel
    @10
    @20
    @15
    wb
    @0
    @1
    @6
    @18
    simplll
    @8
    @3
    cV
    @11
    @16
    sselda
    @8
    @10
    @18
    @17
    adantr
    @11
    @5
    @13
    @12
    cV
    cW
    @14
    @22
    @21
    ocvss.v
    @23
    iporthcom
    syl3anc
    mpbid
    ralrimiva
    vy
    @5
    @3
    @13
    @12
    c.pe
    cV
    cW
    @14
    ocvss.v
    @21
    @22
    @23
    ocvss.o
    elocv
    syl3anbrc
    ex
    ssrdv
end
