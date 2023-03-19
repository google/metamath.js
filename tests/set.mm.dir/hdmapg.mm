include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "clsm.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "clspn.mm"
include "coch.mm"
include "c0g.mm"
include "eqid.mm"
include "hdmapglem7.mm"

theorem hdmapg
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hdmapg.h: |- H = ( LHyp ` K )
  assume hdmapg.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapg.v: |- V = ( Base ` U )
  assume hdmapg.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapg.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapg.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapg.x: |- ( ph -> X e. V )
  assume hdmapg.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( G ` ( ( S ` Y ) ` X ) ) = ( ( S ` X ) ` Y ) )

  proof
    wph
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    cU
    cplusg
    cfv
    #
    @0
    cplusg
    cfv
    #
    cU
    clsm
    cfv
    #
    @0
    cS
    cU
    cvsca
    cfv
    #
    @0
    cmulr
    cfv
    #
    cU
    cid
    cK
    cbs
    cfv
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    cres
    cop
    #
    cG
    cH
    cK
    cU
    clspn
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cV
    cW
    cX
    cY
    @0
    c0g
    cfv
    #
    hdmapg.h
    @7
    eqid
    @9
    eqid
    hdmapg.u
    hdmapg.v
    @2
    eqid
    @5
    eqid
    @0
    eqid
    @1
    eqid
    @4
    eqid
    @8
    eqid
    hdmapg.k
    hdmapg.x
    @6
    eqid
    @10
    eqid
    @3
    eqid
    hdmapg.s
    hdmapg.g
    hdmapg.y
    hdmapglem7
end
