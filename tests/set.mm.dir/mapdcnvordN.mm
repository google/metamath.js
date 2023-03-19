include "ccnv.mm"
include "cfv.mm"
include "wss.mm"
include "cdvh.mm"
include "clss.mm"
include "eqid.mm"
include "mapdcnvcl.mm"
include "mapdord.mm"
include "mapdcnvid2.mm"
include "sseq12d.mm"
include "bitr3d.mm"

theorem mapdcnvordN
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


  assert |- ( ph -> ( ( `' M ` X ) C_ ( `' M ` Y ) <-> X C_ Y ) )

  proof
    wph
    cX
    cM
    ccnv
    #
    cfv
    #
    cM
    cfv
    #
    cY
    @0
    cfv
    #
    cM
    cfv
    #
    wss
    @1
    @3
    wss
    cX
    cY
    wss
    wph
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clss
    cfv
    #
    @5
    cH
    cK
    cM
    cW
    @1
    @3
    mapdcnvord.h
    @5
    eqid
    #
    @6
    eqid
    #
    mapdcnvord.m
    mapdcnvord.k
    wph
    @6
    @5
    cH
    cK
    cM
    cW
    cX
    mapdcnvord.h
    mapdcnvord.m
    @7
    @8
    mapdcnvord.k
    mapdcnvord.x
    mapdcnvcl
    wph
    @6
    @5
    cH
    cK
    cM
    cW
    cY
    mapdcnvord.h
    mapdcnvord.m
    @7
    @8
    mapdcnvord.k
    mapdcnvord.y
    mapdcnvcl
    mapdord
    wph
    @2
    cX
    @4
    cY
    wph
    cH
    cK
    cM
    cW
    cX
    mapdcnvord.h
    mapdcnvord.m
    mapdcnvord.k
    mapdcnvord.x
    mapdcnvid2
    wph
    cH
    cK
    cM
    cW
    cY
    mapdcnvord.h
    mapdcnvord.m
    mapdcnvord.k
    mapdcnvord.y
    mapdcnvid2
    sseq12d
    bitr3d
end
