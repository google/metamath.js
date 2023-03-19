include "crn.mm"
include "cdvh.mm"
include "cfv.mm"
include "cld.mm"
include "clss.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cpw.mm"
include "cin.mm"
include "eqid.mm"
include "mapdrn.mm"
include "lcdlss.mm"
include "eqtr4d.mm"

theorem mapdrn2
  let wph: wff ph
  let cC: class C
  let cT: class T
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let vf: setvar f
  assume mapdrn2.h: |- H = ( LHyp ` K )
  assume mapdrn2.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdrn2.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdrn2.t: |- T = ( LSubSp ` C )
  assume mapdrn2.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ran M = T )

  proof
    wph
    cM
    crn
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cld
    cfv
    #
    clss
    cfv
    #
    vf
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
    @5
    cfv
    @4
    wceq
    vf
    @0
    clfn
    cfv
    #
    crab
    #
    cpw
    cin
    cT
    wph
    @7
    @1
    @2
    @0
    vf
    @6
    cH
    cK
    @3
    cM
    @5
    cW
    mapdrn2.h
    @5
    eqid
    #
    mapdrn2.m
    @0
    eqid
    #
    @6
    eqid
    #
    @3
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    @7
    eqid
    #
    mapdrn2.k
    mapdrn
    wph
    @7
    cC
    @1
    cT
    @2
    @0
    vf
    @6
    cH
    cK
    @3
    @5
    cW
    mapdrn2.h
    @8
    mapdrn2.c
    mapdrn2.t
    @9
    @10
    @11
    @12
    @13
    @14
    mapdrn2.k
    lcdlss
    eqtr4d
end
