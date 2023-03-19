include "cfv.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wpss.mm"
include "mapdord.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "anbi12d.mm"
include "df-pss.mm"
include "3bitr4g.mm"

theorem mapdsord
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  assume mapdcnvcl.h: |- H = ( LHyp ` K )
  assume mapdcnvcl.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdcnvcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdcnvcl.s: |- S = ( LSubSp ` U )
  assume mapdcnvcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcl.x: |- ( ph -> X e. S )
  assume mapdsord.x: |- ( ph -> Y e. S )


  assert |- ( ph -> ( ( M ` X ) C. ( M ` Y ) <-> X C. Y ) )

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
    @0
    @1
    wne
    #
    wa
    cX
    cY
    wss
    #
    cX
    cY
    wne
    #
    wa
    @0
    @1
    wpss
    cX
    cY
    wpss
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
    mapdcnvcl.h
    mapdcnvcl.u
    mapdcnvcl.s
    mapdcnvcl.m
    mapdcnvcl.k
    mapdcl.x
    mapdsord.x
    mapdord
    wph
    @0
    @1
    cX
    cY
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    cY
    mapdcnvcl.h
    mapdcnvcl.u
    mapdcnvcl.s
    mapdcnvcl.m
    mapdcnvcl.k
    mapdcl.x
    mapdsord.x
    mapd11
    necon3bid
    anbi12d
    @0
    @1
    df-pss
    cX
    cY
    df-pss
    3bitr4g
end
