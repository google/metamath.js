include "cdvh.mm"
include "cfv.mm"
include "cld.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "clvec.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval.mm"
include "wcel.mm"
include "clss.mm"
include "dvhlvec.mm"
include "lduallvec.mm"
include "lclkr.mm"
include "lsslvec.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem lcdlvec
  let wph: wff ph
  let cC: class C
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume lcdlmod.h: |- H = ( LHyp ` K )
  assume lcdlmod.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlmod.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> C e. LVec )

  proof
    wph
    cC
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cld
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
    @4
    cfv
    @3
    wceq
    vf
    @0
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    clvec
    wph
    cC
    @1
    @0
    vf
    @5
    cH
    cK
    @2
    @4
    cW
    chlt
    lcdlmod.h
    @4
    eqid
    #
    lcdlmod.c
    @0
    eqid
    #
    @5
    eqid
    #
    @2
    eqid
    #
    @1
    eqid
    #
    lcdlmod.k
    lcdval
    wph
    @1
    clvec
    wcel
    @6
    @1
    clss
    cfv
    #
    wcel
    @7
    clvec
    wcel
    wph
    @1
    @0
    @12
    wph
    @0
    cH
    cK
    cW
    lcdlmod.h
    @9
    lcdlmod.k
    dvhlvec
    lduallvec
    wph
    @6
    @1
    @13
    @0
    vf
    @5
    cH
    cK
    @2
    @4
    cW
    lcdlmod.h
    @9
    @8
    @10
    @11
    @12
    @13
    eqid
    #
    @6
    eqid
    lcdlmod.k
    lclkr
    @13
    @6
    @1
    @7
    @7
    eqid
    @14
    lsslvec
    syl2anc
    eqeltrd
end
