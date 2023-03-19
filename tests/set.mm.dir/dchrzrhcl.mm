include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "eqid.mm"
include "dchrf.mm"
include "cz.mm"
include "cn0.mm"
include "wcel.mm"
include "wfo.mm"
include "wf.mm"
include "cn.mm"
include "dchrrcl.mm"
include "nnnn0.mm"
include "3syl.mm"
include "znzrhfo.mm"
include "fof.mm"
include "ffvelrnd.mm"

theorem dchrzrhcl
  let wph: wff ph
  let cA: class A
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
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrelbas4.l: |- L = ( ZRHom ` Z )
  assume dchrzrh1.x: |- ( ph -> X e. D )
  assume dchrzrh1.a: |- ( ph -> A e. ZZ )


  assert |- ( ph -> ( X ` ( L ` A ) ) e. CC )

  proof
    wph
    cZ
    cbs
    cfv
    #
    cc
    cA
    cL
    cfv
    cX
    wph
    @0
    cD
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    @0
    eqid
    #
    dchrzrh1.x
    dchrf
    wph
    cz
    @0
    cA
    cL
    wph
    cN
    cn0
    wcel
    #
    cz
    @0
    cL
    wfo
    cz
    @0
    cL
    wf
    wph
    cX
    cD
    wcel
    cN
    cn
    wcel
    @2
    dchrzrh1.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    cN
    nnnn0
    3syl
    @0
    cL
    cN
    cZ
    dchrmhm.z
    @1
    dchrelbas4.l
    znzrhfo
    cz
    @0
    cL
    fof
    3syl
    dchrzrh1.a
    ffvelrnd
    ffvelrnd
end
