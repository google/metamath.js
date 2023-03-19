include "cin.mm"
include "clcd.mm"
include "cfv.mm"
include "clss.mm"
include "crn.mm"
include "clmod.mm"
include "wcel.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "mapdrn2.mm"
include "eleqtrd.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"

theorem mapdincl
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdincl.h: |- H = ( LHyp ` K )
  assume mapdincl.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdincl.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdincl.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdincl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdincl.x: |- ( ph -> X e. ran M )
  assume mapdincl.y: |- ( ph -> Y e. ran M )


  assert |- ( ph -> ( X i^i Y ) e. ran M )

  proof
    wph
    cX
    cY
    cin
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    clss
    cfv
    #
    cM
    crn
    #
    wph
    @1
    clmod
    wcel
    cX
    @2
    wcel
    cY
    @2
    wcel
    @0
    @2
    wcel
    wph
    @1
    cH
    cK
    cW
    mapdincl.h
    @1
    eqid
    #
    mapdincl.k
    lcdlmod
    wph
    cX
    @3
    @2
    mapdincl.x
    wph
    @1
    @2
    cH
    cK
    cM
    cW
    mapdincl.h
    mapdincl.m
    @4
    @2
    eqid
    #
    mapdincl.k
    mapdrn2
    #
    eleqtrd
    wph
    cY
    @3
    @2
    mapdincl.y
    @6
    eleqtrd
    @2
    cX
    cY
    @1
    @5
    lssincl
    syl3anc
    @6
    eleqtrrd
end
