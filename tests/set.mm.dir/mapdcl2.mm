include "cfv.mm"
include "crn.mm"
include "mapdcl.mm"
include "mapdrn2.mm"
include "eleqtrd.mm"

theorem mapdcl2
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  assume mapdlss.h: |- H = ( LHyp ` K )
  assume mapdlss.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdlss.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdlss.s: |- S = ( LSubSp ` U )
  assume mapdlss.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdlss.t: |- T = ( LSubSp ` C )
  assume mapdlss.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdlss.r: |- ( ph -> R e. S )


  assert |- ( ph -> ( M ` R ) e. T )

  proof
    wph
    cR
    cM
    cfv
    cM
    crn
    cT
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cR
    mapdlss.h
    mapdlss.m
    mapdlss.u
    mapdlss.s
    mapdlss.k
    mapdlss.r
    mapdcl
    wph
    cC
    cT
    cH
    cK
    cM
    cW
    mapdlss.h
    mapdlss.m
    mapdlss.c
    mapdlss.t
    mapdlss.k
    mapdrn2
    eleqtrd
end
