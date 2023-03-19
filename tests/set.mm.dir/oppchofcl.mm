include "coppc.mm"
include "cfv.mm"
include "cxpc.mm"
include "co.mm"
include "cfunc.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
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
include "hofcl.mm"
include "2oppchomf.mm"
include "a1i.mm"
include "ccomf.mm"
include "2oppccomf.mm"
include "eqidd.mm"
include "xpcpropd.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"

theorem oppchofcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cM: class M
  let cO: class O
  let cV: class V
  assume oppchofcl.o: |- O = ( oppCat ` C )
  assume oppchofcl.m: |- M = ( HomF ` O )
  assume oppchofcl.d: |- D = ( SetCat ` U )
  assume oppchofcl.c: |- ( ph -> C e. Cat )
  assume oppchofcl.u: |- ( ph -> U e. V )
  assume oppchofcl.h: |- ( ph -> ran ( Homf ` C ) C_ U )


  assert |- ( ph -> M e. ( ( C Xc. O ) Func D ) )

  proof
    wph
    cM
    cO
    coppc
    cfv
    #
    cO
    cxpc
    co
    #
    cD
    cfunc
    co
    cC
    cO
    cxpc
    co
    #
    cD
    cfunc
    co
    wph
    cO
    cD
    cU
    cM
    @0
    cV
    oppchofcl.m
    @0
    eqid
    #
    oppchofcl.d
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    #
    oppchofcl.c
    cC
    cO
    oppchofcl.o
    oppccat
    syl
    #
    oppchofcl.u
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
    @8
    ctpos
    #
    crn
    #
    @7
    @9
    @10
    @6
    cC
    @8
    cO
    oppchofcl.o
    @8
    eqid
    #
    oppchomf
    rneqi
    @8
    cdm
    #
    wrel
    #
    @11
    @9
    wceq
    @14
    cC
    cbs
    cfv
    #
    @15
    cxp
    #
    wrel
    @15
    @15
    relxp
    @13
    @16
    @8
    @16
    wfn
    @13
    @16
    wceq
    @15
    cC
    @8
    @12
    @15
    eqid
    homffn
    @16
    @8
    fndm
    ax-mp
    releqi
    mpbir
    @8
    rntpos
    ax-mp
    eqtr3i
    oppchofcl.h
    syl5eqss
    hofcl
    wph
    @2
    @1
    cD
    cfunc
    wph
    cC
    @0
    cO
    cO
    ccat
    @8
    @0
    chomf
    cfv
    wceq
    wph
    cC
    cO
    oppchofcl.o
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
    oppchofcl.o
    2oppccomf
    a1i
    wph
    @6
    eqidd
    wph
    cO
    ccomf
    cfv
    eqidd
    oppchofcl.c
    wph
    @4
    @0
    ccat
    wcel
    @5
    cO
    @0
    @3
    oppccat
    syl
    @5
    @5
    xpcpropd
    oveq1d
    eleqtrrd
end
