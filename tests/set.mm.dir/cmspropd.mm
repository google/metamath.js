include "cmt.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "wa.mm"
include "ccms.mm"
include "mspropd.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "iscms.mm"
include "3bitr4g.mm"

theorem cmspropd
  let wph: wff ph
  let cB: class B
  let cK: class K
  let cL: class L
  assume cmspropd.1: |- ( ph -> B = ( Base ` K ) )
  assume cmspropd.2: |- ( ph -> B = ( Base ` L ) )
  assume cmspropd.3: |- ( ph -> ( ( dist ` K ) |` ( B X. B ) ) = ( ( dist ` L ) |` ( B X. B ) ) )
  assume cmspropd.4: |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )


  assert |- ( ph -> ( K e. CMetSp <-> L e. CMetSp ) )

  proof
    wph
    cK
    cmt
    wcel
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @2
    cxp
    #
    cres
    #
    @2
    cms
    cfv
    #
    wcel
    #
    wa
    cL
    cmt
    wcel
    #
    cL
    cds
    cfv
    #
    cL
    cbs
    cfv
    #
    @9
    cxp
    #
    cres
    #
    @9
    cms
    cfv
    #
    wcel
    #
    wa
    cK
    ccms
    wcel
    cL
    ccms
    wcel
    wph
    @0
    @7
    @6
    @13
    wph
    cB
    cK
    cL
    cmspropd.1
    cmspropd.2
    cmspropd.3
    cmspropd.4
    mspropd
    wph
    @4
    @11
    @5
    @12
    wph
    @8
    cB
    cB
    cxp
    #
    cres
    #
    @4
    @11
    wph
    @1
    @14
    cres
    @15
    @4
    cmspropd.3
    wph
    @14
    @3
    @1
    wph
    cB
    @2
    cmspropd.1
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @14
    @10
    @8
    wph
    cB
    @9
    cmspropd.2
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @2
    @9
    cms
    wph
    cB
    @2
    @9
    cmspropd.1
    cmspropd.2
    eqtr3d
    fveq2d
    eleq12d
    anbi12d
    @4
    cK
    @2
    @2
    eqid
    @4
    eqid
    iscms
    @11
    cL
    @9
    @9
    eqid
    @11
    eqid
    iscms
    3bitr4g
end
