include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "dochord.mm"
include "anbi12d.mm"
include "eqcom.mm"
include "eqss.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "bicomd.mm"

theorem doch11
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume doch11.h: |- H = ( LHyp ` K )
  assume doch11.i: |- I = ( ( DIsoH ` K ) ` W )
  assume doch11.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume doch11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume doch11.x: |- ( ph -> X e. ran I )
  assume doch11.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( ( ._|_ ` X ) = ( ._|_ ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cY
    wceq
    #
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    wceq
    #
    wph
    cY
    cX
    wss
    #
    cX
    cY
    wss
    #
    wa
    #
    @1
    @2
    wss
    #
    @2
    @1
    wss
    #
    wa
    @0
    @3
    wph
    @4
    @7
    @5
    @8
    wph
    cH
    cI
    cK
    c.pe
    cW
    cY
    cX
    doch11.h
    doch11.i
    doch11.o
    doch11.k
    doch11.y
    doch11.x
    dochord
    wph
    cH
    cI
    cK
    c.pe
    cW
    cX
    cY
    doch11.h
    doch11.i
    doch11.o
    doch11.k
    doch11.x
    doch11.y
    dochord
    anbi12d
    @0
    cY
    cX
    wceq
    @6
    cX
    cY
    eqcom
    cY
    cX
    eqss
    bitri
    @1
    @2
    eqss
    3bitr4g
    bicomd
end
