include "cmul.mm"
include "co.mm"
include "cfv.mm"
include "cmulr.mm"
include "zring.mm"
include "crh.mm"
include "wcel.mm"
include "cz.mm"
include "wceq.mm"
include "crg.mm"
include "ccrg.mm"
include "cn0.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "eqid.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "cbs.mm"
include "dchrmhm.mm"
include "sseldi.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "eqtrd.mm"

theorem dchrzrhmul
  let wph: wff ph
  let cA: class A
  let cC: class C
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
  assume dchrzrh1.c: |- ( ph -> C e. ZZ )


  assert |- ( ph -> ( X ` ( L ` ( A x. C ) ) ) = ( ( X ` ( L ` A ) ) x. ( X ` ( L ` C ) ) ) )

  proof
    wph
    cA
    cC
    cmul
    co
    cL
    cfv
    #
    cX
    cfv
    cA
    cL
    cfv
    #
    cC
    cL
    cfv
    #
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    @1
    cX
    cfv
    @2
    cX
    cfv
    cmul
    co
    #
    wph
    @0
    @4
    cX
    wph
    cL
    zring
    cZ
    crh
    co
    wcel
    #
    cA
    cz
    wcel
    cC
    cz
    wcel
    @0
    @4
    wceq
    wph
    cZ
    crg
    wcel
    #
    @7
    wph
    cZ
    ccrg
    wcel
    #
    @8
    wph
    cN
    cn0
    wcel
    @9
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
    syl
    cZ
    crngring
    syl
    cZ
    cL
    dchrelbas4.l
    zrhrhm
    syl
    #
    dchrzrh1.a
    dchrzrh1.c
    cA
    cC
    zring
    cZ
    cmul
    @3
    cL
    cz
    zringbas
    zringmulr
    @3
    eqid
    #
    rhmmul
    syl3anc
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
    @1
    cZ
    cbs
    cfv
    #
    wcel
    @2
    @15
    wcel
    @5
    @6
    wceq
    wph
    cD
    @14
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
    wph
    cz
    @15
    cA
    cL
    wph
    @7
    cz
    @15
    cL
    wf
    @10
    cz
    @15
    zring
    cZ
    cL
    zringbas
    @15
    eqid
    #
    rhmf
    syl
    #
    dchrzrh1.a
    ffvelrnd
    wph
    cz
    @15
    cC
    cL
    @17
    dchrzrh1.c
    ffvelrnd
    @15
    @3
    cmul
    @12
    @13
    cX
    @1
    @2
    @15
    cZ
    @12
    @12
    eqid
    #
    @16
    mgpbas
    cZ
    @3
    @12
    @18
    @11
    mgpplusg
    ccnfld
    cmul
    @13
    @13
    eqid
    cnfldmul
    mgpplusg
    mhmlin
    syl3anc
    eqtrd
end
