include "clsa.mm"
include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "clsh.mm"
include "wcel.mm"
include "eqid.mm"
include "mapdordlem2.mm"

theorem mapdord
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume mapdord.h: |- H = ( LHyp ` K )
  assume mapdord.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdord.s: |- S = ( LSubSp ` U )
  assume mapdord.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdord.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdord.x: |- ( ph -> X e. S )
  assume mapdord.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( ( M ` X ) C_ ( M ` Y ) <-> X C_ Y ) )

  proof
    wph
    cU
    clsa
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
    @3
    cfv
    #
    @2
    wceq
    vg
    cU
    clfn
    cfv
    #
    crab
    #
    cS
    @4
    cU
    clsh
    cfv
    #
    wcel
    vg
    @5
    crab
    #
    cU
    vg
    @5
    cH
    @7
    cK
    @1
    cM
    @3
    cW
    cX
    cY
    mapdord.h
    mapdord.u
    mapdord.s
    mapdord.m
    mapdord.k
    mapdord.x
    mapdord.y
    @3
    eqid
    @0
    eqid
    @5
    eqid
    @7
    eqid
    @1
    eqid
    @8
    eqid
    @6
    eqid
    mapdordlem2
end
