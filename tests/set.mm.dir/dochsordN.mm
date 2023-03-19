include "wss.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wpss.mm"
include "dochord.mm"
include "wceq.mm"
include "doch11.mm"
include "eqcom.mm"
include "syl6rbb.mm"
include "necon3bid.mm"
include "anbi12d.mm"
include "df-pss.mm"
include "3bitr4g.mm"

theorem dochsordN
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


  assert |- ( ph -> ( X C. Y <-> ( ._|_ ` Y ) C. ( ._|_ ` X ) ) )

  proof
    wph
    cX
    cY
    wss
    #
    cX
    cY
    wne
    #
    wa
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wss
    #
    @2
    @3
    wne
    #
    wa
    cX
    cY
    wpss
    @2
    @3
    wpss
    wph
    @0
    @4
    @1
    @5
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
    wph
    cX
    cY
    @2
    @3
    wph
    @2
    @3
    wceq
    cY
    cX
    wceq
    cX
    cY
    wceq
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
    doch11
    cY
    cX
    eqcom
    syl6rbb
    necon3bid
    anbi12d
    cX
    cY
    df-pss
    @2
    @3
    df-pss
    3bitr4g
end
