include "ccnv.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "mapdcnvordN.mm"
include "anbi12d.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem mapdcnv11N
  let wph: wff ph
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdcnvord.h: |- H = ( LHyp ` K )
  assume mapdcnvord.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdcnvord.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcnvord.x: |- ( ph -> X e. ran M )
  assume mapdcnvord.y: |- ( ph -> Y e. ran M )


  assert |- ( ph -> ( ( `' M ` X ) = ( `' M ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cM
    ccnv
    #
    cfv
    #
    cY
    @0
    cfv
    #
    wss
    #
    @2
    @1
    wss
    #
    wa
    cX
    cY
    wss
    #
    cY
    cX
    wss
    #
    wa
    @1
    @2
    wceq
    cX
    cY
    wceq
    wph
    @3
    @5
    @4
    @6
    wph
    cH
    cK
    cM
    cW
    cX
    cY
    mapdcnvord.h
    mapdcnvord.m
    mapdcnvord.k
    mapdcnvord.x
    mapdcnvord.y
    mapdcnvordN
    wph
    cH
    cK
    cM
    cW
    cY
    cX
    mapdcnvord.h
    mapdcnvord.m
    mapdcnvord.k
    mapdcnvord.y
    mapdcnvord.x
    mapdcnvordN
    anbi12d
    @1
    @2
    eqss
    cX
    cY
    eqss
    3bitr4g
end
