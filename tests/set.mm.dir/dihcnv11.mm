include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wb.mm"
include "crn.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "dih11.mm"
include "syl3anc.mm"
include "dihcnvid2.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem dihcnv11
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihcnv11.h: |- H = ( LHyp ` K )
  assume dihcnv11.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihcnv11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihcnv11.x: |- ( ph -> X e. ran I )
  assume dihcnv11.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( ( `' I ` X ) = ( `' I ` Y ) <-> X = Y ) )

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
    wceq
    #
    @1
    @3
    wceq
    #
    cX
    cY
    wceq
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
    dihcnv11.k
    wph
    @7
    cX
    cI
    crn
    #
    wcel
    #
    @9
    dihcnv11.k
    dihcnv11.x
    @8
    cH
    cI
    cK
    cW
    cX
    @8
    eqid
    #
    dihcnv11.h
    dihcnv11.i
    dihcnvcl
    syl2anc
    wph
    @7
    cY
    @11
    wcel
    #
    @10
    dihcnv11.k
    dihcnv11.y
    @8
    cH
    cI
    cK
    cW
    cY
    @13
    dihcnv11.h
    dihcnv11.i
    dihcnvcl
    syl2anc
    @8
    cH
    cI
    cK
    cW
    @1
    @3
    @13
    dihcnv11.h
    dihcnv11.i
    dih11
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
    dihcnv11.k
    dihcnv11.x
    cH
    cI
    cK
    cW
    cX
    dihcnv11.h
    dihcnv11.i
    dihcnvid2
    syl2anc
    wph
    @7
    @14
    @4
    cY
    wceq
    dihcnv11.k
    dihcnv11.y
    cH
    cI
    cK
    cW
    cY
    dihcnv11.h
    dihcnv11.i
    dihcnvid2
    syl2anc
    eqeq12d
    bitr3d
end
