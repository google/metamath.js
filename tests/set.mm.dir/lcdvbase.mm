include "cld.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ldualvbase.mm"
include "syl5sseqr.mm"
include "ressbas2.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem lcdvbase
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume lcdvbase.h: |- H = ( LHyp ` K )
  assume lcdvbase.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcdvbase.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvbase.v: |- V = ( Base ` C )
  assume lcdvbase.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvbase.f: |- F = ( LFnl ` U )
  assume lcdvbase.l: |- L = ( LKer ` U )
  assume lcdvbase.b: |- B = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcdvbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint F f
  disjoint K f
  disjoint W f
  assert |- ( ph -> V = B )

  proof
    wph
    cV
    cU
    cld
    cfv
    #
    cB
    cress
    co
    #
    cbs
    cfv
    #
    cB
    wph
    cV
    cC
    cbs
    cfv
    @2
    lcdvbase.v
    wph
    cC
    @1
    cbs
    wph
    cB
    cC
    @0
    cU
    vf
    cF
    cH
    cK
    cL
    c.pe
    cW
    chlt
    lcdvbase.h
    lcdvbase.o
    lcdvbase.c
    lcdvbase.u
    lcdvbase.f
    lcdvbase.l
    @0
    eqid
    #
    lcdvbase.k
    lcdvbase.b
    lcdval2
    fveq2d
    syl5eq
    wph
    cB
    @0
    cbs
    cfv
    #
    wss
    cB
    @2
    wceq
    wph
    cF
    cB
    @4
    cB
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @5
    wceq
    #
    vf
    cF
    crab
    cF
    lcdvbase.b
    @6
    vf
    cF
    ssrab2
    eqsstri
    wph
    @0
    cF
    @4
    cU
    clmod
    lcdvbase.f
    @3
    @4
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lcdvbase.h
    lcdvbase.u
    lcdvbase.k
    dvhlmod
    ldualvbase
    syl5sseqr
    cB
    @4
    @1
    @0
    @1
    eqid
    @7
    ressbas2
    syl
    eqtr4d
end
