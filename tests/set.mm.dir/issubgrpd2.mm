include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "ne0i.mm"
include "syl.mm"
include "wceq.mm"
include "oveqd.mm"
include "ad2antrr.mm"
include "3expa.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "eqid.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem issubgrpd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cI: class I
  let c.0: class .0.
  assume issubgrpd.s: |- ( ph -> S = ( I |`s D ) )
  assume issubgrpd.z: |- ( ph -> .0. = ( 0g ` I ) )
  assume issubgrpd.p: |- ( ph -> .+ = ( +g ` I ) )
  assume issubgrpd.ss: |- ( ph -> D C_ ( Base ` I ) )
  assume issubgrpd.zcl: |- ( ph -> .0. e. D )
  assume issubgrpd.acl: |- ( ( ph /\ x e. D /\ y e. D ) -> ( x .+ y ) e. D )
  assume issubgrpd.ncl: |- ( ( ph /\ x e. D ) -> ( ( invg ` I ) ` x ) e. D )
  assume issubgrpd.g: |- ( ph -> I e. Grp )

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
  assert |- ( ph -> D e. ( SubGrp ` I ) )

  proof
    wph
    cD
    cI
    csubg
    cfv
    wcel
    #
    cD
    cI
    cbs
    cfv
    #
    wss
    #
    cD
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    cplusg
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
    #
    @4
    cI
    cminusg
    cfv
    #
    cfv
    cD
    wcel
    #
    wa
    #
    vx
    cD
    wral
    #
    issubgrpd.ss
    wph
    c.0
    cD
    wcel
    @3
    issubgrpd.zcl
    cD
    c.0
    ne0i
    syl
    wph
    @12
    vx
    cD
    wph
    @4
    cD
    wcel
    #
    wa
    #
    @9
    @11
    @15
    @8
    vy
    cD
    @15
    @5
    cD
    wcel
    #
    wa
    @4
    @5
    c.pl
    co
    #
    @7
    cD
    wph
    @17
    @7
    wceq
    @14
    @16
    wph
    c.pl
    @6
    @4
    @5
    issubgrpd.p
    oveqd
    ad2antrr
    wph
    @14
    @16
    @17
    cD
    wcel
    issubgrpd.acl
    3expa
    eqeltrrd
    ralrimiva
    issubgrpd.ncl
    jca
    ralrimiva
    wph
    cI
    cgrp
    wcel
    @0
    @2
    @3
    @13
    w3a
    wb
    issubgrpd.g
    vx
    vy
    @1
    @6
    cD
    cI
    @10
    @1
    eqid
    @6
    eqid
    @10
    eqid
    issubg2
    syl
    mpbir3and
end
