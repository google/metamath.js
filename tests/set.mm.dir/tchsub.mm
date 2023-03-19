include "csg.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqid.mm"
include "tchbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "tchplusg.mm"
include "grpsubpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem tchsub
  let cG: class G
  let c.mi: class .-
  let cW: class W
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.xi: class .,
  let cF: class F
  let cV: class V
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchsub.v: |- .- = ( -g ` W )


  assert |- .- = ( -g ` G )

  proof
    c.mi
    cW
    csg
    cfv
    #
    cG
    csg
    cfv
    #
    tchsub.v
    @0
    @1
    wceq
    wtru
    cW
    cG
    cW
    cbs
    cfv
    #
    cG
    cbs
    cfv
    wceq
    wtru
    cG
    @2
    cW
    tchval.n
    @2
    eqid
    tchbas
    a1i
    cW
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    wceq
    wtru
    @3
    cG
    cW
    tchval.n
    @3
    eqid
    tchplusg
    a1i
    grpsubpropd
    trud
    eqtri
end
