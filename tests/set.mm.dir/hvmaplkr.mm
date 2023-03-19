include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "csca.mm"
include "cbs.mm"
include "crio.mm"
include "cmpt.mm"
include "chlt.mm"
include "eqid.mm"
include "hvmapfval.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "clfn.mm"
include "crab.mm"
include "cld.mm"
include "c0g.mm"
include "lcfrlem11.mm"
include "eqtrd.mm"

theorem hvmaplkr
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vj: setvar j
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vf: setvar f
  assume hvmaplkr.h: |- H = ( LHyp ` K )
  assume hvmaplkr.o: |- O = ( ( ocH ` K ) ` W )
  assume hvmaplkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmaplkr.v: |- V = ( Base ` U )
  assume hvmaplkr.z: |- .0. = ( 0g ` U )
  assume hvmaplkr.l: |- L = ( LKer ` U )
  assume hvmaplkr.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmaplkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hvmaplkr.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( L ` ( M ` X ) ) = ( O ` { X } ) )

  proof
    wph
    cX
    cM
    cfv
    #
    cL
    cfv
    cX
    vx
    cV
    c.0
    csn
    cdif
    vv
    cV
    vv
    cv
    vt
    cv
    vj
    cv
    vx
    cv
    #
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
    @1
    csn
    cO
    cfv
    wrex
    vj
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    crio
    cmpt
    cmpt
    #
    cfv
    #
    cL
    cfv
    cX
    csn
    cO
    cfv
    wph
    @0
    @7
    cL
    wph
    cX
    cM
    @6
    wph
    vx
    vv
    vt
    chlt
    @3
    @5
    @4
    @2
    cU
    vj
    cH
    cK
    cM
    cO
    cV
    cW
    c.0
    hvmaplkr.h
    hvmaplkr.u
    hvmaplkr.o
    hvmaplkr.v
    @3
    eqid
    #
    @2
    eqid
    #
    hvmaplkr.z
    @4
    eqid
    #
    @5
    eqid
    #
    hvmaplkr.m
    hvmaplkr.k
    hvmapfval
    fveq1d
    fveq2d
    wph
    vx
    vt
    vv
    vf
    cv
    cL
    cfv
    #
    cO
    cfv
    cO
    cfv
    @12
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cU
    cld
    cfv
    #
    @3
    @15
    c0g
    cfv
    #
    @5
    @4
    @2
    cU
    vf
    vj
    @13
    cH
    @6
    cK
    cL
    cO
    cV
    cW
    cX
    c.0
    hvmaplkr.h
    hvmaplkr.o
    hvmaplkr.u
    hvmaplkr.v
    @8
    @9
    @10
    @11
    hvmaplkr.z
    @13
    eqid
    hvmaplkr.l
    @15
    eqid
    @16
    eqid
    @14
    eqid
    @6
    eqid
    hvmaplkr.k
    hvmaplkr.x
    lcfrlem11
    eqtrd
end
