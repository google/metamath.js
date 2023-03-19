include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "crg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "issubgrpd2.mm"
include "eqeltrrd.mm"
include "wa.mm"
include "oveqdr.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "cbs.mm"
include "eqid.mm"
include "issubrg2.mm"
include "mpbir3and.mm"

theorem issubrngd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let c.0: class .0.
  assume issubrngd.s: |- ( ph -> S = ( I |`s D ) )
  assume issubrngd.z: |- ( ph -> .0. = ( 0g ` I ) )
  assume issubrngd.p: |- ( ph -> .+ = ( +g ` I ) )
  assume issubrngd.ss: |- ( ph -> D C_ ( Base ` I ) )
  assume issubrngd.zcl: |- ( ph -> .0. e. D )
  assume issubrngd.acl: |- ( ( ph /\ x e. D /\ y e. D ) -> ( x .+ y ) e. D )
  assume issubrngd.ncl: |- ( ( ph /\ x e. D ) -> ( ( invg ` I ) ` x ) e. D )
  assume issubrngd.o: |- ( ph -> .1. = ( 1r ` I ) )
  assume issubrngd.t: |- ( ph -> .x. = ( .r ` I ) )
  assume issubrngd.ocl: |- ( ph -> .1. e. D )
  assume issubrngd.tcl: |- ( ( ph /\ x e. D /\ y e. D ) -> ( x .x. y ) e. D )
  assume issubrngd.g: |- ( ph -> I e. Ring )

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint D x
  disjoint D y
  disjoint I x
  disjoint I y
  disjoint .+ x
  disjoint .+ y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint .x. x
  disjoint .x. y
  assert |- ( ph -> D e. ( SubRing ` I ) )

  proof
    wph
    cD
    cI
    csubrg
    cfv
    wcel
    #
    cD
    cI
    csubg
    cfv
    wcel
    #
    cI
    cur
    cfv
    #
    cD
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    cmulr
    cfv
    #
    co
    #
    cD
    wcel
    #
    vy
    cD
    wral
    vx
    cD
    wral
    #
    wph
    vx
    vy
    cD
    c.pl
    cS
    cI
    c.0
    issubrngd.s
    issubrngd.z
    issubrngd.p
    issubrngd.ss
    issubrngd.zcl
    issubrngd.acl
    issubrngd.ncl
    wph
    cI
    crg
    wcel
    #
    cI
    cgrp
    wcel
    issubrngd.g
    cI
    ringgrp
    syl
    issubgrpd2
    wph
    c.1
    @2
    cD
    issubrngd.o
    issubrngd.ocl
    eqeltrrd
    wph
    @8
    vx
    vy
    cD
    cD
    wph
    @4
    cD
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    wa
    @4
    @5
    c.x
    co
    #
    @7
    cD
    wph
    @13
    vx
    vy
    c.x
    @6
    issubrngd.t
    oveqdr
    wph
    @11
    @12
    @14
    cD
    wcel
    issubrngd.tcl
    3expb
    eqeltrrd
    ralrimivva
    wph
    @10
    @0
    @1
    @3
    @9
    w3a
    wb
    issubrngd.g
    vx
    vy
    cD
    cI
    cbs
    cfv
    #
    cI
    @6
    @2
    @15
    eqid
    @2
    eqid
    @6
    eqid
    issubrg2
    syl
    mpbir3and
end
