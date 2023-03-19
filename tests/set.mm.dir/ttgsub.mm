include "csg.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqid.mm"
include "ttgbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "ttgplusg.mm"
include "grpsubpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem ttgsub
  let cG: class G
  let cH: class H
  let c.mi: class .-
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgsub.1: |- .- = ( -g ` H )


  assert |- .- = ( -g ` G )

  proof
    c.mi
    cH
    csg
    cfv
    #
    cG
    csg
    cfv
    #
    ttgsub.1
    @0
    @1
    wceq
    wtru
    cH
    cG
    cH
    cbs
    cfv
    #
    cG
    cbs
    cfv
    wceq
    wtru
    @2
    cG
    cH
    ttgval.n
    @2
    eqid
    ttgbas
    a1i
    cH
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
    cH
    ttgval.n
    @3
    eqid
    ttgplusg
    a1i
    grpsubpropd
    trud
    eqtri
end
