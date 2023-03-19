include "cphl.mm"
include "wcel.mm"
include "wb.mm"
include "wtru.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "eqidd.mm"
include "wceq.mm"
include "eqid.mm"
include "tchbas.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "tchplusg.mm"
include "oveqdr.mm"
include "tchsca.mm"
include "cvsca.mm"
include "tchvsca.mm"
include "cip.mm"
include "tchip.mm"
include "phlpropd.mm"
include "trud.mm"

theorem tchphl
  let cG: class G
  let cW: class W
  let c.mi: class .-
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


  assert |- ( W e. PreHil <-> G e. PreHil )

  proof
    cW
    cphl
    wcel
    cG
    cphl
    wcel
    wb
    wtru
    vx
    vy
    cW
    cbs
    cfv
    #
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @1
    cW
    cG
    wtru
    @0
    eqidd
    @0
    cG
    cbs
    cfv
    wceq
    wtru
    cG
    @0
    cW
    tchval.n
    @0
    eqid
    tchbas
    a1i
    wtru
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    @0
    wcel
    #
    wa
    #
    vx
    vy
    cW
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    #
    @6
    @7
    wceq
    wtru
    @6
    cG
    cW
    tchval.n
    @6
    eqid
    tchplusg
    a1i
    oveqdr
    wtru
    @1
    eqidd
    @1
    cG
    csca
    cfv
    wceq
    wtru
    @1
    cG
    cW
    tchval.n
    @1
    eqid
    tchsca
    a1i
    @2
    eqid
    wtru
    @3
    @2
    wcel
    @4
    wa
    vx
    vy
    cW
    cvsca
    cfv
    #
    cG
    cvsca
    cfv
    #
    @8
    @9
    wceq
    wtru
    @8
    cG
    cW
    tchval.n
    @8
    eqid
    tchvsca
    a1i
    oveqdr
    wtru
    @5
    vx
    vy
    cW
    cip
    cfv
    #
    cG
    cip
    cfv
    #
    @10
    @11
    wceq
    wtru
    @10
    cG
    cW
    tchval.n
    @10
    eqid
    tchip
    a1i
    oveqdr
    phlpropd
    trud
end
