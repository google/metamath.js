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
include "sseq2d.mm"
include "bitrd.mm"

theorem dochord2N
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


  assert |- ( ph -> ( ( ._|_ ` X ) C_ Y <-> ( ._|_ ` Y ) C_ X ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    cY
    wss
    cY
    c.pe
    cfv
    #
    @0
    c.pe
    cfv
    #
    wss
    @1
    cX
    wss
    wph
    cH
    cI
    cK
    c.pe
    cW
    @0
    cY
    doch11.h
    doch11.i
    doch11.o
    doch11.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
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
    cX
    @4
    clss
    cfv
    #
    wcel
    #
    @6
    wph
    @3
    cX
    @7
    wcel
    #
    @9
    doch11.k
    doch11.x
    @8
    @4
    cH
    cI
    cK
    cW
    cX
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
    cX
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
    cX
    doch11.h
    doch11.i
    @11
    @13
    doch11.o
    dochcl
    syl2anc
    doch11.y
    dochord
    wph
    @2
    cX
    @1
    wph
    @3
    @10
    @2
    cX
    wceq
    doch11.k
    doch11.x
    cH
    cI
    cK
    c.pe
    cW
    cX
    doch11.h
    doch11.i
    doch11.o
    dochoc
    syl2anc
    sseq2d
    bitrd
end
