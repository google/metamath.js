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
include "wcel.mm"
include "ccnv.mm"
include "eqid.mm"
include "mapd1o.mm"
include "f1ocnvfv1.mm"
include "syl2anc.mm"

theorem mapdcnvid1N
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


  assert |- ( ph -> ( `' M ` ( M ` X ) ) = X )

  proof
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
    @4
    cfv
    @3
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
    cX
    cS
    wcel
    cX
    cM
    cfv
    cM
    ccnv
    cfv
    cX
    wceq
    wph
    @6
    @0
    cS
    @1
    cU
    vg
    @5
    cH
    cK
    @2
    cM
    @4
    cW
    mapdcnvcl.h
    @4
    eqid
    mapdcnvcl.m
    mapdcnvcl.u
    mapdcnvcl.s
    @5
    eqid
    @2
    eqid
    @0
    eqid
    @1
    eqid
    @6
    eqid
    mapdcnvcl.k
    mapd1o
    mapdcl.x
    cS
    @7
    cX
    cM
    f1ocnvfv1
    syl2anc
end
