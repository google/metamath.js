include "crg.mm"
include "wcel.mm"
include "opprring.mm"
include "coppr.mm"
include "cfv.mm"
include "eqid.mm"
include "wb.mm"
include "wtru.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "opprbas.mm"
include "a1i.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "oppradd.mm"
include "oveqi.mm"
include "cmulr.mm"
include "opprmul.mm"
include "eqtr2i.mm"
include "ringpropd.mm"
include "trud.mm"
include "sylibr.mm"
include "impbii.mm"

theorem opprringb
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )


  assert |- ( R e. Ring <-> O e. Ring )

  proof
    cR
    crg
    wcel
    #
    cO
    crg
    wcel
    #
    cR
    cO
    opprbas.1
    opprring
    @1
    cO
    coppr
    cfv
    #
    crg
    wcel
    #
    @0
    cO
    @2
    @2
    eqid
    #
    opprring
    @0
    @3
    wb
    wtru
    vx
    vy
    cR
    cbs
    cfv
    #
    cR
    @2
    wtru
    @5
    eqidd
    @5
    @2
    cbs
    cfv
    wceq
    wtru
    @5
    cO
    @2
    @4
    @5
    cR
    cO
    opprbas.1
    @5
    eqid
    #
    opprbas
    #
    opprbas
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    @8
    @9
    @2
    cplusg
    cfv
    #
    co
    wceq
    wtru
    @8
    @5
    wcel
    @9
    @5
    wcel
    wa
    wa
    #
    @10
    @11
    @8
    @9
    @10
    cO
    @2
    @4
    @10
    cR
    cO
    opprbas.1
    @10
    eqid
    oppradd
    oppradd
    oveqi
    a1i
    @8
    @9
    cR
    cmulr
    cfv
    #
    co
    #
    @8
    @9
    @2
    cmulr
    cfv
    #
    co
    #
    wceq
    @12
    @16
    @9
    @8
    cO
    cmulr
    cfv
    #
    co
    @14
    @5
    cO
    @15
    @17
    @2
    @8
    @9
    @7
    @17
    eqid
    #
    @4
    @15
    eqid
    opprmul
    @5
    cR
    @17
    @13
    cO
    @9
    @8
    @6
    @13
    eqid
    opprbas.1
    @18
    opprmul
    eqtr2i
    a1i
    ringpropd
    trud
    sylibr
    impbii
end
