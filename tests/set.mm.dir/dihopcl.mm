include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "dihssxp.mm"
include "sseldd.mm"
include "opelxp.mm"
include "sylib.mm"

theorem dihopcl
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihopcl.b: |- B = ( Base ` K )
  assume dihopcl.h: |- H = ( LHyp ` K )
  assume dihopcl.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihopcl.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihopcl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihopcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihopcl.x: |- ( ph -> X e. B )
  assume dihopcl.y: |- ( ph -> <. F , S >. e. ( I ` X ) )


  assert |- ( ph -> ( F e. T /\ S e. E ) )

  proof
    wph
    cF
    cS
    cop
    #
    cT
    cE
    cxp
    #
    wcel
    cF
    cT
    wcel
    cS
    cE
    wcel
    wa
    wph
    cX
    cI
    cfv
    @1
    @0
    wph
    cB
    cT
    cE
    cH
    cI
    cK
    cW
    cX
    dihopcl.b
    dihopcl.h
    dihopcl.t
    dihopcl.e
    dihopcl.i
    dihopcl.k
    dihopcl.x
    dihssxp
    dihopcl.y
    sseldd
    cF
    cS
    cT
    cE
    opelxp
    sylib
end
