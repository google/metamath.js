include "ccnv.mm"
include "cfv.mm"
include "wss.mm"
include "wbr.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wb.mm"
include "crn.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "dihord.mm"
include "syl3anc.mm"
include "wceq.mm"
include "dihcnvid2.mm"
include "sseq12d.mm"
include "bitr3d.mm"

theorem dihcnvord
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihcnvord.l: |- .<_ = ( le ` K )
  assume dihcnvord.h: |- H = ( LHyp ` K )
  assume dihcnvord.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihcnvord.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihcnvord.x: |- ( ph -> X e. ran I )
  assume dihcnvord.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( ( `' I ` X ) .<_ ( `' I ` Y ) <-> X C_ Y ) )

  proof
    wph
    cX
    cI
    ccnv
    #
    cfv
    #
    cI
    cfv
    #
    cY
    @0
    cfv
    #
    cI
    cfv
    #
    wss
    #
    @1
    @3
    c.le
    wbr
    #
    cX
    cY
    wss
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    @8
    wcel
    #
    @5
    @6
    wb
    dihcnvord.k
    wph
    @7
    cX
    cI
    crn
    #
    wcel
    #
    @9
    dihcnvord.k
    dihcnvord.x
    @8
    cH
    cI
    cK
    cW
    cX
    @8
    eqid
    #
    dihcnvord.h
    dihcnvord.i
    dihcnvcl
    syl2anc
    wph
    @7
    cY
    @11
    wcel
    #
    @10
    dihcnvord.k
    dihcnvord.y
    @8
    cH
    cI
    cK
    cW
    cY
    @13
    dihcnvord.h
    dihcnvord.i
    dihcnvcl
    syl2anc
    @8
    cH
    cI
    cK
    c.le
    cW
    @1
    @3
    @13
    dihcnvord.l
    dihcnvord.h
    dihcnvord.i
    dihord
    syl3anc
    wph
    @2
    cX
    @4
    cY
    wph
    @7
    @12
    @2
    cX
    wceq
    dihcnvord.k
    dihcnvord.x
    cH
    cI
    cK
    cW
    cX
    dihcnvord.h
    dihcnvord.i
    dihcnvid2
    syl2anc
    wph
    @7
    @14
    @4
    cY
    wceq
    dihcnvord.k
    dihcnvord.y
    cH
    cI
    cK
    cW
    cY
    dihcnvord.h
    dihcnvord.i
    dihcnvid2
    syl2anc
    sseq12d
    bitr3d
end
