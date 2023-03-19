include "cfv.mm"
include "wss.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdvh.mm"
include "cbs.mm"
include "crn.mm"
include "clss.mm"
include "eqid.mm"
include "dihrnlss.mm"
include "syl2anc.mm"
include "lssss.mm"
include "syl.mm"
include "dochcl.mm"
include "dochord.mm"
include "wceq.mm"
include "dochoc.mm"
include "sseq1d.mm"
include "bitrd.mm"

theorem dochord3
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


  assert |- ( ph -> ( X C_ ( ._|_ ` Y ) <-> Y C_ ( ._|_ ` X ) ) )

  proof
    wph
    cX
    cY
    c.pe
    cfv
    #
    wss
    @0
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wss
    cY
    @2
    wss
    wph
    cH
    cI
    cK
    c.pe
    cW
    cX
    @0
    doch11.h
    doch11.i
    doch11.o
    doch11.k
    doch11.x
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cY
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    wss
    #
    @0
    cI
    crn
    #
    wcel
    doch11.k
    wph
    cY
    @4
    clss
    cfv
    #
    wcel
    #
    @6
    wph
    @3
    cY
    @7
    wcel
    #
    @9
    doch11.k
    doch11.y
    @8
    @4
    cH
    cI
    cK
    cW
    cY
    doch11.h
    @4
    eqid
    #
    doch11.i
    @8
    eqid
    #
    dihrnlss
    syl2anc
    @8
    cY
    @5
    @4
    @5
    eqid
    #
    @12
    lssss
    syl
    @4
    cH
    cI
    cK
    c.pe
    @5
    cW
    cY
    doch11.h
    doch11.i
    @11
    @13
    doch11.o
    dochcl
    syl2anc
    dochord
    wph
    @1
    cY
    @2
    wph
    @3
    @10
    @1
    cY
    wceq
    doch11.k
    doch11.y
    cH
    cI
    cK
    c.pe
    cW
    cY
    doch11.h
    doch11.i
    doch11.o
    dochoc
    syl2anc
    sseq1d
    bitrd
end
