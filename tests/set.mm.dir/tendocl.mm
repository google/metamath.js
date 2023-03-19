include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wf.mm"
include "tendof.mm"
include "3adant3.mm"
include "simp3.mm"
include "ffvelrnd.mm"

theorem tendocl
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cU: class U
  let cG: class G
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ S e. E /\ F e. T ) -> ( S ` F ) e. T )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
    cT
    cT
    cF
    cS
    @0
    @1
    cT
    cT
    cS
    wf
    @2
    cS
    cT
    cE
    cH
    cK
    cV
    cW
    tendof.h
    tendof.t
    tendof.e
    tendof
    3adant3
    @0
    @1
    @2
    simp3
    ffvelrnd
end
