include "cops.mm"
include "wcel.mm"
include "cpo.mm"
include "cbs.mm"
include "cfv.mm"
include "club.mm"
include "cdm.mm"
include "cglb.mm"
include "w3a.mm"
include "cv.mm"
include "coc.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "cjn.mm"
include "co.mm"
include "cp1.mm"
include "cmee.mm"
include "cp0.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "isopos.mm"
include "simpl1.mm"
include "sylbi.mm"

theorem opposet
  let cK: class K
  let vx: setvar x
  let vy: setvar y


  assert |- ( K e. OP -> K e. Poset )

  proof
    cK
    cops
    wcel
    cK
    cpo
    wcel
    #
    cK
    cbs
    cfv
    #
    cK
    club
    cfv
    #
    cdm
    wcel
    #
    @1
    cK
    cglb
    cfv
    #
    cdm
    wcel
    #
    w3a
    vx
    cv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    @1
    wcel
    @8
    @7
    cfv
    @6
    wceq
    @6
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @9
    @7
    cfv
    @8
    @10
    wbr
    wi
    w3a
    @6
    @8
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    @6
    @8
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    w3a
    vy
    @1
    wral
    vx
    @1
    wral
    #
    wa
    @0
    vx
    vy
    @1
    @2
    @12
    @4
    @11
    cK
    @10
    @13
    @7
    @14
    @1
    eqid
    @2
    eqid
    @4
    eqid
    @10
    eqid
    @7
    eqid
    @11
    eqid
    @13
    eqid
    @14
    eqid
    @12
    eqid
    isopos
    @0
    @3
    @5
    @15
    simpl1
    sylbi
end
