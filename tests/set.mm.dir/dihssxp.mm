include "cfv.mm"
include "cdvh.mm"
include "cbs.mm"
include "cxp.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "eqid.mm"
include "dihss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "dvhvbase.mm"
include "syl.mm"
include "sseqtrd.mm"

theorem dihssxp
  let wph: wff ph
  let cB: class B
  let cT: class T
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihssxp.b: |- B = ( Base ` K )
  assume dihssxp.h: |- H = ( LHyp ` K )
  assume dihssxp.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihssxp.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihssxp.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihssxp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihssxp.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( I ` X ) C_ ( T X. E ) )

  proof
    wph
    cX
    cI
    cfv
    #
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    cT
    cE
    cxp
    #
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
    cB
    wcel
    @0
    @2
    wss
    dihssxp.k
    dihssxp.x
    cB
    @1
    cH
    cI
    cK
    @2
    cW
    cX
    dihssxp.b
    dihssxp.h
    dihssxp.i
    @1
    eqid
    #
    @2
    eqid
    #
    dihss
    syl2anc
    wph
    @4
    @2
    @3
    wceq
    dihssxp.k
    cT
    @1
    cE
    cH
    cK
    @2
    cW
    chlt
    dihssxp.h
    dihssxp.t
    dihssxp.e
    @5
    @6
    dvhvbase
    syl
    sseqtrd
end
