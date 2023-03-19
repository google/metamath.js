include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "csn.mm"
include "coch.mm"
include "wrex.mm"
include "cbs.mm"
include "crio.mm"
include "cmpt.mm"
include "chlt.mm"
include "eqid.mm"
include "hvmapval.mm"
include "fveq1d.mm"
include "dochfl1.mm"
include "eqtrd.mm"

theorem hvmapidN
  let wph: wff ph
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vj: setvar j
  let vt: setvar t
  let vv: setvar v
  assume hvmapid.h: |- H = ( LHyp ` K )
  assume hvmapid.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmapid.v: |- V = ( Base ` U )
  assume hvmapid.z: |- .0. = ( 0g ` U )
  assume hvmapid.s: |- S = ( Scalar ` U )
  assume hvmapid.i: |- .1. = ( 1r ` S )
  assume hvmapid.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmapid.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hvmapid.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( ( M ` X ) ` X ) = .1. )

  proof
    wph
    cX
    cX
    cM
    cfv
    #
    cfv
    cX
    vv
    cV
    vv
    cv
    vt
    cv
    vj
    cv
    cX
    cU
    cvsca
    cfv
    #
    co
    cU
    cplusg
    cfv
    #
    co
    wceq
    vt
    cX
    csn
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    wrex
    vj
    cS
    cbs
    cfv
    #
    crio
    cmpt
    #
    cfv
    c.1
    wph
    cX
    @0
    @5
    wph
    vv
    vt
    chlt
    @2
    @4
    cS
    @1
    cU
    vj
    cH
    cK
    cM
    @3
    cV
    cW
    cX
    c.0
    hvmapid.h
    hvmapid.u
    @3
    eqid
    #
    hvmapid.v
    @2
    eqid
    #
    @1
    eqid
    #
    hvmapid.z
    hvmapid.s
    @4
    eqid
    #
    hvmapid.m
    hvmapid.k
    hvmapid.x
    hvmapval
    fveq1d
    wph
    vt
    vv
    cS
    @2
    @4
    @1
    cU
    c.1
    vj
    @5
    cH
    cK
    @3
    cV
    cW
    cX
    c.0
    hvmapid.h
    @6
    hvmapid.u
    hvmapid.v
    @7
    @8
    hvmapid.z
    hvmapid.s
    @9
    hvmapid.i
    hvmapid.k
    hvmapid.x
    @5
    eqid
    dochfl1
    eqtrd
end
