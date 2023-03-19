include "cgrp.mm"
include "wcel.mm"
include "cmt.mm"
include "cnm.mm"
include "cfv.mm"
include "csg.mm"
include "ccom.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cngp.mm"
include "wa.mm"
include "wb.mm"
include "mspropd.mm"
include "adantr.mm"
include "simpr.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "adantlr.mm"
include "nmpropd2.mm"
include "grpsubpropd2.mm"
include "coeq12d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "3eqtr3d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "pm5.32da.mm"
include "grppropd.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "eqid.mm"
include "isngp2.mm"

theorem ngppropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume ngppropd.1: |- ( ph -> B = ( Base ` K ) )
  assume ngppropd.2: |- ( ph -> B = ( Base ` L ) )
  assume ngppropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume ngppropd.4: |- ( ph -> ( ( dist ` K ) |` ( B X. B ) ) = ( ( dist ` L ) |` ( B X. B ) ) )
  assume ngppropd.5: |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( K e. NrmGrp <-> L e. NrmGrp ) )

  proof
    wph
    cK
    cgrp
    wcel
    #
    cK
    cmt
    wcel
    #
    cK
    cnm
    cfv
    #
    cK
    csg
    cfv
    #
    ccom
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @6
    cxp
    #
    cres
    #
    wceq
    #
    w3a
    #
    cL
    cgrp
    wcel
    #
    cL
    cmt
    wcel
    #
    cL
    cnm
    cfv
    #
    cL
    csg
    cfv
    #
    ccom
    #
    cL
    cds
    cfv
    #
    cL
    cbs
    cfv
    #
    @17
    cxp
    #
    cres
    #
    wceq
    #
    w3a
    #
    cK
    cngp
    wcel
    cL
    cngp
    wcel
    wph
    @0
    @1
    @9
    wa
    #
    wa
    #
    @11
    @12
    @20
    wa
    #
    wa
    #
    @10
    @21
    wph
    @23
    @0
    @24
    wa
    @25
    wph
    @0
    @22
    @24
    wph
    @0
    wa
    #
    @1
    @12
    @9
    @20
    wph
    @1
    @12
    wb
    @0
    wph
    cB
    cK
    cL
    ngppropd.1
    ngppropd.2
    ngppropd.4
    ngppropd.5
    mspropd
    adantr
    @26
    @4
    @15
    @8
    @19
    @26
    @2
    @13
    @3
    @14
    @26
    vx
    vy
    cB
    cK
    cL
    wph
    cB
    @6
    wceq
    @0
    ngppropd.1
    adantr
    #
    wph
    cB
    @17
    wceq
    @0
    ngppropd.2
    adantr
    #
    wph
    @0
    simpr
    #
    wph
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    @30
    @31
    cK
    cplusg
    cfv
    co
    @30
    @31
    cL
    cplusg
    cfv
    co
    wceq
    @0
    ngppropd.3
    adantlr
    #
    wph
    @5
    cB
    cB
    cxp
    #
    cres
    #
    @16
    @33
    cres
    #
    wceq
    @0
    ngppropd.4
    adantr
    nmpropd2
    @26
    vx
    vy
    cB
    cK
    cL
    @27
    @28
    @29
    @32
    grpsubpropd2
    coeq12d
    wph
    @8
    @19
    wceq
    @0
    wph
    @34
    @35
    @8
    @19
    ngppropd.4
    wph
    @33
    @7
    @5
    wph
    cB
    @6
    ngppropd.1
    sqxpeqd
    reseq2d
    wph
    @33
    @18
    @16
    wph
    cB
    @17
    ngppropd.2
    sqxpeqd
    reseq2d
    3eqtr3d
    adantr
    eqeq12d
    anbi12d
    pm5.32da
    wph
    @0
    @11
    @24
    wph
    vx
    vy
    cB
    cK
    cL
    ngppropd.1
    ngppropd.2
    ngppropd.3
    grppropd
    anbi1d
    bitrd
    @0
    @1
    @9
    3anass
    @11
    @12
    @20
    3anass
    3bitr4g
    @5
    @8
    cK
    @3
    @2
    @6
    @2
    eqid
    @3
    eqid
    @5
    eqid
    @6
    eqid
    @8
    eqid
    isngp2
    @16
    @19
    cL
    @14
    @13
    @17
    @13
    eqid
    @14
    eqid
    @16
    eqid
    @17
    eqid
    @19
    eqid
    isngp2
    3bitr4g
end
