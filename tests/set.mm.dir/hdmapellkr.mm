include "cfv.mm"
include "clk.mm"
include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "clfn.mm"
include "clmod.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "clcd.mm"
include "cbs.mm"
include "hdmapcl.mm"
include "lcdvbaselfl.mm"
include "ellkr2.mm"
include "hdmaplkr.mm"
include "eleq2d.mm"
include "bitr3d.mm"

theorem hdmapellkr
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmapellkr.h: |- H = ( LHyp ` K )
  assume hdmapellkr.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapellkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapellkr.v: |- V = ( Base ` U )
  assume hdmapellkr.r: |- R = ( Scalar ` U )
  assume hdmapellkr.z: |- .0. = ( 0g ` R )
  assume hdmapellkr.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapellkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapellkr.x: |- ( ph -> X e. V )
  assume hdmapellkr.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( ( S ` X ) ` Y ) = .0. <-> Y e. ( O ` { X } ) ) )

  proof
    wph
    cY
    cX
    cS
    cfv
    #
    cU
    clk
    cfv
    #
    cfv
    #
    wcel
    cY
    @0
    cfv
    c.0
    wceq
    cY
    cX
    csn
    cO
    cfv
    #
    wcel
    wph
    cR
    cU
    clfn
    cfv
    #
    @0
    @1
    cV
    cU
    cY
    clmod
    c.0
    hdmapellkr.v
    hdmapellkr.r
    hdmapellkr.z
    @4
    eqid
    #
    @1
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    hdmapellkr.h
    hdmapellkr.u
    hdmapellkr.k
    dvhlmod
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    @4
    cH
    cK
    @7
    cbs
    cfv
    #
    cW
    @0
    hdmapellkr.h
    @7
    eqid
    #
    @8
    eqid
    #
    hdmapellkr.u
    @5
    hdmapellkr.k
    wph
    @7
    @8
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmapellkr.h
    hdmapellkr.u
    hdmapellkr.v
    @9
    @10
    hdmapellkr.s
    hdmapellkr.k
    hdmapellkr.x
    hdmapcl
    lcdvbaselfl
    hdmapellkr.y
    ellkr2
    wph
    @2
    @3
    cY
    wph
    cS
    cU
    @4
    cH
    cK
    cO
    cV
    cW
    cX
    @1
    hdmapellkr.h
    hdmapellkr.o
    hdmapellkr.u
    hdmapellkr.v
    @5
    @6
    hdmapellkr.s
    hdmapellkr.k
    hdmapellkr.x
    hdmaplkr
    eleq2d
    bitr3d
end
