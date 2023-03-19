include "cdvh.mm"
include "cfv.mm"
include "clss.mm"
include "crn.mm"
include "wf1o.mm"
include "wcel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cld.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "clfn.mm"
include "crab.mm"
include "cpw.mm"
include "cin.mm"
include "wf1.mm"
include "eqid.mm"
include "mapd1o.mm"
include "f1of1.mm"
include "f1f1orn.mm"
include "3syl.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"

theorem mapdcnvid2
  let wph: wff ph
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let vg: setvar g
  assume mapdcnvid2.h: |- H = ( LHyp ` K )
  assume mapdcnvid2.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdcnvid2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcnvid2.x: |- ( ph -> X e. ran M )


  assert |- ( ph -> ( M ` ( `' M ` X ) ) = X )

  proof
    wph
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clss
    cfv
    #
    cM
    crn
    #
    cM
    wf1o
    #
    cX
    @2
    wcel
    cX
    cM
    ccnv
    cfv
    cM
    cfv
    cX
    wceq
    wph
    @1
    @0
    cld
    cfv
    #
    clss
    cfv
    #
    vg
    cv
    @0
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
    @8
    cfv
    @7
    wceq
    vg
    @0
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
    @11
    cM
    wf1
    @3
    wph
    @10
    @4
    @1
    @5
    @0
    vg
    @9
    cH
    cK
    @6
    cM
    @8
    cW
    mapdcnvid2.h
    @8
    eqid
    mapdcnvid2.m
    @0
    eqid
    @1
    eqid
    @9
    eqid
    @6
    eqid
    @4
    eqid
    @5
    eqid
    @10
    eqid
    mapdcnvid2.k
    mapd1o
    @1
    @11
    cM
    f1of1
    @1
    @11
    cM
    f1f1orn
    3syl
    mapdcnvid2.x
    @1
    @2
    cX
    cM
    f1ocnvfv2
    syl2anc
end
