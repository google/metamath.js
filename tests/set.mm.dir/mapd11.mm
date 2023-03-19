include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "mapdord.mm"
include "anbi12d.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem mapd11
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


  assert |- ( ph -> ( ( M ` X ) = ( M ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    wss
    #
    @1
    @0
    wss
    #
    wa
    cX
    cY
    wss
    #
    cY
    cX
    wss
    #
    wa
    @0
    @1
    wceq
    cX
    cY
    wceq
    wph
    @2
    @4
    @3
    @5
    wph
    cS
    cU
    cH
    cK
    cM
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
    mapdord
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cY
    cX
    mapdord.h
    mapdord.u
    mapdord.s
    mapdord.m
    mapdord.k
    mapdord.y
    mapdord.x
    mapdord
    anbi12d
    @0
    @1
    eqss
    cX
    cY
    eqss
    3bitr4g
end
