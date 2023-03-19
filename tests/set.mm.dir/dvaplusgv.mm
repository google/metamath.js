include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "dvaplusg.mm"
include "fveq1d.mm"
include "3adantr3.mm"
include "simpr3.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "coex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem dvaplusgv
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  assume dvafplus.h: |- H = ( LHyp ` K )
  assume dvafplus.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafplus.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvafplus.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafplus.f: |- F = ( Scalar ` U )
  assume dvafplus.p: |- .+ = ( +g ` F )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( R e. E /\ S e. E /\ G e. T ) ) -> ( ( R .+ S ) ` G ) = ( ( R ` G ) o. ( S ` G ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cR
    cE
    wcel
    #
    cS
    cE
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    wa
    #
    cG
    cR
    cS
    c.pl
    co
    #
    cfv
    #
    cG
    vf
    cT
    vf
    cv
    #
    cR
    cfv
    #
    @7
    cS
    cfv
    #
    ccom
    #
    cmpt
    #
    cfv
    #
    cG
    cR
    cfv
    #
    cG
    cS
    cfv
    #
    ccom
    #
    @0
    @1
    @2
    @6
    @12
    wceq
    @3
    @0
    @1
    @2
    wa
    wa
    cG
    @5
    @11
    c.pl
    cR
    cS
    cT
    cU
    vf
    cE
    cF
    cH
    cK
    cV
    cW
    dvafplus.h
    dvafplus.t
    dvafplus.e
    dvafplus.u
    dvafplus.f
    dvafplus.p
    dvaplusg
    fveq1d
    3adantr3
    @4
    @3
    @12
    @15
    wceq
    @0
    @1
    @2
    @3
    simpr3
    vf
    cG
    @10
    @15
    cT
    @11
    @7
    cG
    wceq
    @8
    @13
    @9
    @14
    @7
    cG
    cR
    fveq2
    @7
    cG
    cS
    fveq2
    coeq12d
    @11
    eqid
    @13
    @14
    cG
    cR
    fvex
    cG
    cS
    fvex
    coex
    fvmpt
    syl
    eqtrd
end
