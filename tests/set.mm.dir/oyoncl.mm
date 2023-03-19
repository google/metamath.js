include "coppc.mm"
include "cfv.mm"
include "cfuc.mm"
include "co.mm"
include "cfunc.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "eqid.mm"
include "chomf.mm"
include "crn.mm"
include "ctpos.mm"
include "oppchomf.mm"
include "rneqi.mm"
include "cdm.mm"
include "wrel.mm"
include "wceq.mm"
include "cbs.mm"
include "cxp.mm"
include "relxp.mm"
include "wfn.mm"
include "homffn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "releqi.mm"
include "mpbir.mm"
include "rntpos.mm"
include "eqtr3i.mm"
include "syl5eqss.mm"
include "yoncl.mm"
include "2oppchomf.mm"
include "a1i.mm"
include "ccomf.mm"
include "2oppccomf.mm"
include "eqidd.mm"
include "setccat.mm"
include "fucpropd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"

theorem oyoncl
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  let cY: class Y
  assume oyoncl.o: |- O = ( oppCat ` C )
  assume oyoncl.y: |- Y = ( Yon ` O )
  assume oyoncl.c: |- ( ph -> C e. Cat )
  assume oyoncl.s: |- S = ( SetCat ` U )
  assume oyoncl.u: |- ( ph -> U e. V )
  assume oyoncl.h: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume oyoncl.q: |- Q = ( C FuncCat S )


  assert |- ( ph -> Y e. ( O Func Q ) )

  proof
    wph
    cY
    cO
    cO
    coppc
    cfv
    #
    cS
    cfuc
    co
    #
    cfunc
    co
    cO
    cQ
    cfunc
    co
    wph
    cO
    @1
    cS
    cU
    @0
    cV
    cY
    oyoncl.y
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    #
    oyoncl.c
    cC
    cO
    oyoncl.o
    oppccat
    syl
    #
    @0
    eqid
    #
    oyoncl.s
    @1
    eqid
    oyoncl.u
    wph
    cO
    chomf
    cfv
    #
    crn
    #
    cC
    chomf
    cfv
    #
    crn
    #
    cU
    @7
    ctpos
    #
    crn
    #
    @6
    @8
    @9
    @5
    cC
    @7
    cO
    oyoncl.o
    @7
    eqid
    #
    oppchomf
    rneqi
    @7
    cdm
    #
    wrel
    #
    @10
    @8
    wceq
    @13
    cC
    cbs
    cfv
    #
    @14
    cxp
    #
    wrel
    @14
    @14
    relxp
    @12
    @15
    @7
    @15
    wfn
    @12
    @15
    wceq
    @14
    cC
    @7
    @11
    @14
    eqid
    homffn
    @15
    @7
    fndm
    ax-mp
    releqi
    mpbir
    @7
    rntpos
    ax-mp
    eqtr3i
    oyoncl.h
    syl5eqss
    yoncl
    wph
    cQ
    @1
    cO
    cfunc
    wph
    cQ
    cC
    cS
    cfuc
    co
    @1
    oyoncl.q
    wph
    cC
    @0
    cS
    cS
    @7
    @0
    chomf
    cfv
    wceq
    wph
    cC
    cO
    oyoncl.o
    2oppchomf
    a1i
    cC
    ccomf
    cfv
    @0
    ccomf
    cfv
    wceq
    wph
    cC
    cO
    oyoncl.o
    2oppccomf
    a1i
    wph
    cS
    chomf
    cfv
    eqidd
    wph
    cS
    ccomf
    cfv
    eqidd
    oyoncl.c
    wph
    @2
    @0
    ccat
    wcel
    @3
    cO
    @0
    @4
    oppccat
    syl
    wph
    cU
    cV
    wcel
    cS
    ccat
    wcel
    oyoncl.u
    cS
    cU
    cV
    oyoncl.s
    setccat
    syl
    #
    @16
    fucpropd
    syl5eq
    oveq2d
    eleqtrrd
end
