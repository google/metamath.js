include "crg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "id.mm"
include "cps1.mm"
include "ply1bascl.mm"
include "eqid.mm"
include "psr1bascl.mm"
include "syl.mm"
include "cmpl.mm"
include "ply1mulr.mm"
include "mplmulr.mm"
include "psropprmul.mm"
include "syl3an.mm"

theorem ply1opprmul
  let cB: class B
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cY: class Y
  let cZ: class Z
  assume ply1opprmul.y: |- Y = ( Poly1 ` R )
  assume ply1opprmul.s: |- S = ( oppR ` R )
  assume ply1opprmul.z: |- Z = ( Poly1 ` S )
  assume ply1opprmul.t: |- .x. = ( .r ` Y )
  assume ply1opprmul.u: |- .xb = ( .r ` Z )
  assume ply1opprmul.b: |- B = ( Base ` Y )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. B ) -> ( F .xb G ) = ( G .x. F ) )

  proof
    cR
    crg
    wcel
    #
    @0
    cF
    cB
    wcel
    #
    cF
    c1o
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    wcel
    #
    cG
    cB
    wcel
    #
    cG
    @3
    wcel
    #
    cF
    cG
    c.xb
    co
    cG
    cF
    c.x
    co
    wceq
    @0
    id
    @1
    cF
    cR
    cps1
    cfv
    #
    cbs
    cfv
    #
    wcel
    @4
    cB
    cY
    cR
    cF
    ply1opprmul.y
    ply1opprmul.b
    ply1bascl
    @8
    @7
    cR
    cF
    @7
    eqid
    #
    @8
    eqid
    #
    psr1bascl
    syl
    @5
    cG
    @8
    wcel
    @6
    cB
    cY
    cR
    cG
    ply1opprmul.y
    ply1opprmul.b
    ply1bascl
    @8
    @7
    cR
    cG
    @9
    @10
    psr1bascl
    syl
    @3
    cR
    cS
    c.xb
    c.x
    cF
    cG
    c1o
    @2
    c1o
    cS
    cmps
    co
    #
    @2
    eqid
    #
    ply1opprmul.s
    @11
    eqid
    #
    cR
    @2
    c.x
    c1o
    c1o
    cR
    cmpl
    co
    #
    @14
    eqid
    #
    @12
    cR
    @14
    c.x
    cY
    ply1opprmul.y
    @15
    ply1opprmul.t
    ply1mulr
    mplmulr
    cS
    @11
    c.xb
    c1o
    c1o
    cS
    cmpl
    co
    #
    @16
    eqid
    #
    @13
    cS
    @16
    c.xb
    cZ
    ply1opprmul.z
    @17
    ply1opprmul.u
    ply1mulr
    mplmulr
    @3
    eqid
    psropprmul
    syl3an
end
