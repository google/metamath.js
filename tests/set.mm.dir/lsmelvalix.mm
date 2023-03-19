include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "lsmelvalx.mm"
include "biimpar.mm"
include "sylan2.mm"

theorem lsmelvalix
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmfval.v: |- B = ( Base ` G )
  assume lsmfval.a: |- .+ = ( +g ` G )
  assume lsmfval.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( G e. V /\ T C_ B /\ U C_ B ) /\ ( X e. T /\ Y e. U ) ) -> ( X .+ Y ) e. ( T .(+) U ) )

  proof
    cX
    cT
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    cG
    cV
    wcel
    cT
    cB
    wss
    cU
    cB
    wss
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    vx
    cv
    vy
    cv
    c.pl
    co
    wceq
    vy
    cU
    wrex
    vx
    cT
    wrex
    #
    @3
    cT
    cU
    c.po
    co
    wcel
    #
    @0
    @1
    @3
    @3
    wceq
    @4
    @3
    eqid
    vx
    vy
    cT
    cU
    cX
    cY
    @3
    c.pl
    rspceov
    mp3an3
    @2
    @5
    @4
    vx
    vy
    cB
    c.pl
    c.po
    cT
    cU
    cG
    cV
    @3
    lsmfval.v
    lsmfval.a
    lsmfval.s
    lsmelvalx
    biimpar
    sylan2
end
