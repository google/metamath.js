include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cmpt.mm"
include "cnm.mm"
include "eqtr3d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "eqidd.mm"
include "grpidpropd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "cgrp.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "nmfval2.mm"
include "syl.mm"
include "grppropd.mm"
include "mpbid.mm"
include "3eqtr4d.mm"

theorem nmpropd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let va: setvar a
  assume nmpropd2.1: |- ( ph -> B = ( Base ` K ) )
  assume nmpropd2.2: |- ( ph -> B = ( Base ` L ) )
  assume nmpropd2.3: |- ( ph -> K e. Grp )
  assume nmpropd2.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume nmpropd2.5: |- ( ph -> ( ( dist ` K ) |` ( B X. B ) ) = ( ( dist ` L ) |` ( B X. B ) ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint a x
  disjoint a y
  disjoint K a
  disjoint L a
  disjoint a ph
  assert |- ( ph -> ( norm ` K ) = ( norm ` L ) )

  proof
    wph
    va
    cK
    cbs
    cfv
    #
    va
    cv
    #
    cK
    c0g
    cfv
    #
    cK
    cds
    cfv
    #
    @0
    @0
    cxp
    #
    cres
    #
    co
    #
    cmpt
    #
    va
    cL
    cbs
    cfv
    #
    @1
    cL
    c0g
    cfv
    #
    cL
    cds
    cfv
    #
    @8
    @8
    cxp
    #
    cres
    #
    co
    #
    cmpt
    #
    cK
    cnm
    cfv
    #
    cL
    cnm
    cfv
    #
    wph
    va
    @0
    @6
    @8
    @13
    wph
    cB
    @0
    @8
    nmpropd2.1
    nmpropd2.2
    eqtr3d
    wph
    @1
    @1
    @2
    @9
    @5
    @12
    wph
    @10
    cB
    cB
    cxp
    #
    cres
    #
    @5
    @12
    wph
    @3
    @17
    cres
    @18
    @5
    nmpropd2.5
    wph
    @17
    @4
    @3
    wph
    cB
    @0
    nmpropd2.1
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @17
    @11
    @10
    wph
    cB
    @8
    nmpropd2.2
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @1
    eqidd
    wph
    vx
    vy
    cB
    cK
    cL
    nmpropd2.1
    nmpropd2.2
    nmpropd2.4
    grpidpropd
    oveq123d
    mpteq12dv
    wph
    cK
    cgrp
    wcel
    #
    @15
    @7
    wceq
    nmpropd2.3
    va
    @3
    @5
    @15
    cK
    @0
    @2
    @15
    eqid
    @0
    eqid
    @2
    eqid
    @3
    eqid
    @5
    eqid
    nmfval2
    syl
    wph
    cL
    cgrp
    wcel
    #
    @16
    @14
    wceq
    wph
    @19
    @20
    nmpropd2.3
    wph
    vx
    vy
    cB
    cK
    cL
    nmpropd2.1
    nmpropd2.2
    nmpropd2.4
    grppropd
    mpbid
    va
    @10
    @12
    @16
    cL
    @8
    @9
    @16
    eqid
    @8
    eqid
    @9
    eqid
    @10
    eqid
    @12
    eqid
    nmfval2
    syl
    3eqtr4d
end
