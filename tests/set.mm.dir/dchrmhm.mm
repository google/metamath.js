include "cmgp.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cbs.mm"
include "cui.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "eqid.mm"
include "dchrrcl.mm"
include "dchrelbas.mm"
include "ibi.mm"
include "simpld.mm"
include "ssriv.mm"

theorem dchrmhm
  let cD: class D
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cB: class B
  let cK: class K
  let cL: class L
  let cU: class U
  let cA: class A
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )


  assert |- D C_ ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) )

  proof
    vx
    cD
    cZ
    cmgp
    cfv
    ccnfld
    cmgp
    cfv
    cmhm
    co
    #
    vx
    cv
    #
    cD
    wcel
    #
    @1
    @0
    wcel
    #
    cZ
    cbs
    cfv
    #
    cZ
    cui
    cfv
    #
    cdif
    cc0
    csn
    cxp
    @1
    wss
    #
    @2
    @3
    @6
    wa
    @2
    @4
    cD
    @5
    cG
    cN
    @1
    cZ
    dchrmhm.g
    dchrmhm.z
    @4
    eqid
    @5
    eqid
    cD
    cG
    cN
    @1
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    dchrmhm.b
    dchrelbas
    ibi
    simpld
    ssriv
end
