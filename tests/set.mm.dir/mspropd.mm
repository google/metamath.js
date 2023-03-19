include "cxme.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "wa.mm"
include "cmt.mm"
include "xmspropd.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "ctopn.mm"
include "eqid.mm"
include "isms.mm"
include "3bitr4g.mm"

theorem mspropd
  let wph: wff ph
  let cB: class B
  let cK: class K
  let cL: class L
  assume xmspropd.1: |- ( ph -> B = ( Base ` K ) )
  assume xmspropd.2: |- ( ph -> B = ( Base ` L ) )
  assume xmspropd.3: |- ( ph -> ( ( dist ` K ) |` ( B X. B ) ) = ( ( dist ` L ) |` ( B X. B ) ) )
  assume xmspropd.4: |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )


  assert |- ( ph -> ( K e. MetSp <-> L e. MetSp ) )

  proof
    wph
    cK
    cxme
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
    cme
    cfv
    #
    wcel
    #
    wa
    cL
    cxme
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
    cme
    cfv
    #
    wcel
    #
    wa
    cK
    cmt
    wcel
    cL
    cmt
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
    xmspropd.1
    xmspropd.2
    xmspropd.3
    xmspropd.4
    xmspropd
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
    xmspropd.3
    wph
    @14
    @3
    @1
    wph
    cB
    @2
    xmspropd.1
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
    xmspropd.2
    sqxpeqd
    reseq2d
    eqtr3d
    wph
    @2
    @9
    cme
    wph
    cB
    @2
    @9
    xmspropd.1
    xmspropd.2
    eqtr3d
    fveq2d
    eleq12d
    anbi12d
    @4
    cK
    ctopn
    cfv
    #
    cK
    @2
    @16
    eqid
    @2
    eqid
    @4
    eqid
    isms
    @11
    cL
    ctopn
    cfv
    #
    cL
    @9
    @17
    eqid
    @9
    eqid
    @11
    eqid
    isms
    3bitr4g
end
