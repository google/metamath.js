include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wf.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "istendo.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "syl6bi.mm"
include "3imp.mm"

theorem tendotp
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  assume tendoset.l: |- .<_ = ( le ` K )
  assume tendoset.h: |- H = ( LHyp ` K )
  assume tendoset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoset.r: |- R = ( ( trL ` K ) ` W )
  assume tendoset.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ S e. E /\ F e. T ) -> ( R ` ( S ` F ) ) .<_ ( R ` F ) )

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
    cF
    cS
    cfv
    #
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    c.le
    wbr
    #
    @0
    @1
    cT
    cT
    cS
    wf
    #
    vf
    cv
    #
    vg
    cv
    #
    ccom
    cS
    cfv
    @8
    cS
    cfv
    #
    @9
    cS
    cfv
    ccom
    wceq
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @10
    cR
    cfv
    #
    @8
    cR
    cfv
    #
    c.le
    wbr
    #
    vf
    cT
    wral
    #
    w3a
    @2
    @6
    wi
    #
    cR
    cS
    cT
    vf
    vg
    cE
    cH
    cK
    c.le
    cV
    cW
    tendoset.l
    tendoset.h
    tendoset.t
    tendoset.r
    tendoset.e
    istendo
    @15
    @7
    @16
    @11
    @14
    @6
    vf
    cF
    cT
    @8
    cF
    wceq
    #
    @12
    @4
    @13
    @5
    c.le
    @17
    @10
    @3
    cR
    @8
    cF
    cS
    fveq2
    fveq2d
    @8
    cF
    cR
    fveq2
    breq12d
    rspccv
    3ad2ant3
    syl6bi
    3imp
end
