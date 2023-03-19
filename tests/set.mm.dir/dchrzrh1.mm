include "c1.mm"
include "cfv.mm"
include "cur.mm"
include "cn0.mm"
include "wcel.mm"
include "ccrg.mm"
include "crg.mm"
include "wceq.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "eqid.mm"
include "zrh1.mm"
include "4syl.mm"
include "fveq2d.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "dchrmhm.mm"
include "sseldi.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "eqtrd.mm"

theorem dchrzrh1
  let wph: wff ph
  let cD: class D
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cB: class B
  let cK: class K
  let cU: class U
  let cA: class A
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrelbas4.l: |- L = ( ZRHom ` Z )
  assume dchrzrh1.x: |- ( ph -> X e. D )


  assert |- ( ph -> ( X ` ( L ` 1 ) ) = 1 )

  proof
    wph
    c1
    cL
    cfv
    #
    cX
    cfv
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    c1
    wph
    @0
    @1
    cX
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    cZ
    crg
    wcel
    @0
    @1
    wceq
    wph
    cN
    wph
    cX
    cD
    wcel
    cN
    cn
    wcel
    dchrzrh1.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    nnnn0d
    cN
    cZ
    dchrmhm.z
    zncrng
    cZ
    crngring
    cZ
    @1
    cL
    dchrelbas4.l
    @1
    eqid
    #
    zrh1
    4syl
    fveq2d
    wph
    cX
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
    wcel
    @2
    c1
    wceq
    wph
    cD
    @6
    cX
    cD
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmhm
    dchrzrh1.x
    sseldi
    @4
    @5
    cX
    c1
    @1
    cZ
    @1
    @4
    @4
    eqid
    @3
    ringidval
    ccnfld
    c1
    @5
    @5
    eqid
    cnfld1
    ringidval
    mhm0
    syl
    eqtrd
end
