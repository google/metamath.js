include "ctps.mm"
include "wcel.mm"
include "ctopn.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wceq.mm"
include "wa.mm"
include "cxme.mm"
include "eqtr3d.mm"
include "tpspropd.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "isxms.mm"
include "3bitr4g.mm"

theorem xmspropd
  let wph: wff ph
  let cB: class B
  let cK: class K
  let cL: class L
  assume xmspropd.1: |- ( ph -> B = ( Base ` K ) )
  assume xmspropd.2: |- ( ph -> B = ( Base ` L ) )
  assume xmspropd.3: |- ( ph -> ( ( dist ` K ) |` ( B X. B ) ) = ( ( dist ` L ) |` ( B X. B ) ) )
  assume xmspropd.4: |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )


  assert |- ( ph -> ( K e. *MetSp <-> L e. *MetSp ) )

  proof
    wph
    cK
    ctps
    wcel
    #
    cK
    ctopn
    cfv
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @3
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    wceq
    #
    wa
    cL
    ctps
    wcel
    #
    cL
    ctopn
    cfv
    #
    cL
    cds
    cfv
    #
    cL
    cbs
    cfv
    #
    @11
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    wceq
    #
    wa
    cK
    cxme
    wcel
    cL
    cxme
    wcel
    wph
    @0
    @8
    @7
    @15
    wph
    cK
    cL
    wph
    cB
    @3
    @11
    xmspropd.1
    xmspropd.2
    eqtr3d
    xmspropd.4
    tpspropd
    wph
    @1
    @9
    @6
    @14
    xmspropd.4
    wph
    @5
    @13
    cmopn
    wph
    @10
    cB
    cB
    cxp
    #
    cres
    #
    @5
    @13
    wph
    @2
    @16
    cres
    @17
    @5
    xmspropd.3
    wph
    @16
    @4
    @2
    wph
    cB
    @3
    xmspropd.1
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @16
    @12
    @10
    wph
    cB
    @11
    xmspropd.2
    sqxpeqd
    reseq2d
    eqtr3d
    fveq2d
    eqeq12d
    anbi12d
    @5
    @1
    cK
    @3
    @1
    eqid
    @3
    eqid
    @5
    eqid
    isxms
    @13
    @9
    cL
    @11
    @9
    eqid
    @11
    eqid
    @13
    eqid
    isxms
    3bitr4g
end
