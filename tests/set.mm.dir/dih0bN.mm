include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "cops.mm"
include "simpld.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "dih11.mm"
include "syl3anc.mm"
include "dih0.mm"
include "syl.mm"
include "eqeq2d.mm"
include "bitr3d.mm"

theorem dih0bN
  let wph: wff ph
  let cB: class B
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume dih0b.b: |- B = ( Base ` K )
  assume dih0b.h: |- H = ( LHyp ` K )
  assume dih0b.o: |- .0. = ( 0. ` K )
  assume dih0b.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0b.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0b.z: |- Z = ( 0g ` U )
  assume dih0b.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dih0b.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( X = .0. <-> ( I ` X ) = { Z } ) )

  proof
    wph
    cX
    cI
    cfv
    #
    c.0
    cI
    cfv
    #
    wceq
    #
    cX
    c.0
    wceq
    #
    @0
    cZ
    csn
    #
    wceq
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    c.0
    cB
    wcel
    #
    @2
    @3
    wb
    dih0b.k
    dih0b.x
    wph
    @5
    cK
    cops
    wcel
    @8
    wph
    @5
    @6
    dih0b.k
    simpld
    cK
    hlop
    cB
    cK
    c.0
    dih0b.b
    dih0b.o
    op0cl
    3syl
    cB
    cH
    cI
    cK
    cW
    cX
    c.0
    dih0b.b
    dih0b.h
    dih0b.i
    dih11
    syl3anc
    wph
    @1
    @4
    @0
    wph
    @7
    @1
    @4
    wceq
    dih0b.k
    cU
    cH
    cI
    cK
    cZ
    cW
    c.0
    dih0b.o
    dih0b.h
    dih0b.i
    dih0b.u
    dih0b.z
    dih0
    syl
    eqeq2d
    bitr3d
end
