include "crn.mm"
include "wfn.mm"
include "wf.mm"
include "cld.mm"
include "cfv.mm"
include "clss.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cpw.mm"
include "cin.mm"
include "wf1o.mm"
include "eqid.mm"
include "mapd1o.mm"
include "f1ofn.mm"
include "syl.mm"
include "dffn3.mm"
include "sylib.mm"
include "ffvelrnd.mm"

theorem mapdcl
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let vg: setvar g
  assume mapdcnvcl.h: |- H = ( LHyp ` K )
  assume mapdcnvcl.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdcnvcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdcnvcl.s: |- S = ( LSubSp ` U )
  assume mapdcnvcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcl.x: |- ( ph -> X e. S )


  assert |- ( ph -> ( M ` X ) e. ran M )

  proof
    wph
    cS
    cM
    crn
    #
    cX
    cM
    wph
    cM
    cS
    wfn
    #
    cS
    @0
    cM
    wf
    wph
    cS
    cU
    cld
    cfv
    #
    clss
    cfv
    #
    vg
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @6
    cfv
    @5
    wceq
    vg
    cU
    clfn
    cfv
    #
    crab
    #
    cpw
    cin
    #
    cM
    wf1o
    @1
    wph
    @8
    @2
    cS
    @3
    cU
    vg
    @7
    cH
    cK
    @4
    cM
    @6
    cW
    mapdcnvcl.h
    @6
    eqid
    mapdcnvcl.m
    mapdcnvcl.u
    mapdcnvcl.s
    @7
    eqid
    @4
    eqid
    @2
    eqid
    @3
    eqid
    @8
    eqid
    mapdcnvcl.k
    mapd1o
    cS
    @9
    cM
    f1ofn
    syl
    cS
    cM
    dffn3
    sylib
    mapdcl.x
    ffvelrnd
end
