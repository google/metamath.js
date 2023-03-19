include "wcel.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "wss.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "crab.mm"
include "wa.mm"
include "dchrbas.mm"
include "eleq2d.mm"
include "sseq2.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem dchrelbas
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  let cC: class C
  let cE: class E
  let cY: class Y
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrbas.b: |- D = ( Base ` G )


  assert |- ( ph -> ( X e. D <-> ( X e. ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) ) /\ ( ( B \ U ) X. { 0 } ) C_ X ) ) )

  proof
    wph
    cX
    cD
    wcel
    cX
    cB
    cU
    cdif
    cc0
    csn
    cxp
    #
    vx
    cv
    #
    wss
    #
    vx
    cZ
    cmgp
    cfv
    ccnfld
    cmgp
    cfv
    cmhm
    co
    #
    crab
    #
    wcel
    cX
    @3
    wcel
    @0
    cX
    wss
    #
    wa
    wph
    cD
    @4
    cX
    wph
    vx
    cB
    cD
    cU
    cG
    cN
    cZ
    dchrval.g
    dchrval.z
    dchrval.b
    dchrval.u
    dchrval.n
    dchrbas.b
    dchrbas
    eleq2d
    @2
    @5
    vx
    cX
    @3
    @1
    cX
    @0
    sseq2
    elrab
    syl6bb
end
