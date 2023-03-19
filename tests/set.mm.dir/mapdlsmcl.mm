include "co.mm"
include "clss.mm"
include "cfv.mm"
include "crn.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "mapdrn2.mm"
include "eleqtrd.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"

theorem mapdlsmcl
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdlsmcl.h: |- H = ( LHyp ` K )
  assume mapdlsmcl.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdlsmcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdlsmcl.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdlsmcl.p: |- .(+) = ( LSSum ` C )
  assume mapdlsmcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdlsmcl.x: |- ( ph -> X e. ran M )
  assume mapdlsmcl.y: |- ( ph -> Y e. ran M )


  assert |- ( ph -> ( X .(+) Y ) e. ran M )

  proof
    wph
    cX
    cY
    c.po
    co
    #
    cC
    clss
    cfv
    #
    cM
    crn
    #
    wph
    cC
    clmod
    wcel
    cX
    @1
    wcel
    cY
    @1
    wcel
    @0
    @1
    wcel
    wph
    cC
    cH
    cK
    cW
    mapdlsmcl.h
    mapdlsmcl.c
    mapdlsmcl.k
    lcdlmod
    wph
    cX
    @2
    @1
    mapdlsmcl.x
    wph
    cC
    @1
    cH
    cK
    cM
    cW
    mapdlsmcl.h
    mapdlsmcl.m
    mapdlsmcl.c
    @1
    eqid
    #
    mapdlsmcl.k
    mapdrn2
    #
    eleqtrd
    wph
    cY
    @2
    @1
    mapdlsmcl.y
    @4
    eleqtrd
    c.po
    @1
    cX
    cY
    cC
    @3
    mapdlsmcl.p
    lsmcl
    syl3anc
    @4
    eleqtrrd
end
