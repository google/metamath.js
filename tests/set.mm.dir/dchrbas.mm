include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "wss.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "crab.mm"
include "cop.mm"
include "cplusg.mm"
include "cmul.mm"
include "cof.mm"
include "cres.mm"
include "cpr.mm"
include "eqidd.mm"
include "dchrval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "rabex.mm"
include "eqid.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dchrbas
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  let cC: class C
  let cE: class E
  let cX: class X
  let cY: class Y
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrbas.b: |- D = ( Base ` G )

  disjoint B x
  disjoint N x
  disjoint U x
  disjoint ph x
  disjoint Z x
  disjoint A k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint b n
  disjoint b z
  disjoint D b
  disjoint n z
  disjoint D n
  disjoint D z
  disjoint b x
  disjoint N b
  disjoint n x
  disjoint N n
  disjoint N z
  disjoint U k
  disjoint U y
  disjoint U z
  disjoint C k
  disjoint E k
  disjoint b k
  disjoint b y
  disjoint b ph
  disjoint k n
  disjoint k ph
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Z k
  disjoint Z y
  disjoint Z z
  disjoint Y k
  assert |- ( ph -> D = { x e. ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) ) | ( ( B \ U ) X. { 0 } ) C_ x } )

  proof
    wph
    cG
    cbs
    cfv
    cnx
    cbs
    cfv
    cB
    cU
    cdif
    cc0
    csn
    cxp
    vx
    cv
    wss
    #
    vx
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    #
    crab
    #
    cop
    cnx
    cplusg
    cfv
    cmul
    cof
    @4
    @4
    cxp
    cres
    #
    cop
    cpr
    #
    cbs
    cfv
    #
    cD
    @4
    wph
    cG
    @6
    cbs
    wph
    vx
    cB
    @4
    cU
    cG
    cN
    cZ
    dchrval.g
    dchrval.z
    dchrval.b
    dchrval.u
    dchrval.n
    wph
    @4
    eqidd
    dchrval
    fveq2d
    dchrbas.b
    @4
    cvv
    wcel
    @4
    @7
    wceq
    @0
    vx
    @3
    @1
    @2
    cmhm
    ovex
    rabex
    @4
    @5
    @6
    cvv
    @6
    eqid
    grpbase
    ax-mp
    3eqtr4g
end
