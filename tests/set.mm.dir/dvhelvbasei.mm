include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "opelxpi.mm"
include "adantl.mm"
include "wceq.mm"
include "dvhvbase.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem dvhelvbasei
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assume dvhvbase.h: |- H = ( LHyp ` K )
  assume dvhvbase.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhvbase.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhvbase.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhvbase.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. X /\ W e. H ) /\ ( F e. T /\ S e. E ) ) -> <. F , S >. e. V )

  proof
    cK
    cX
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    cS
    cE
    wcel
    wa
    #
    wa
    cF
    cS
    cop
    #
    cT
    cE
    cxp
    #
    cV
    @1
    @2
    @3
    wcel
    @0
    cF
    cS
    cT
    cE
    opelxpi
    adantl
    @0
    cV
    @3
    wceq
    @1
    cT
    cU
    cE
    cH
    cK
    cV
    cW
    cX
    dvhvbase.h
    dvhvbase.t
    dvhvbase.e
    dvhvbase.u
    dvhvbase.v
    dvhvbase
    adantr
    eleqtrrd
end
