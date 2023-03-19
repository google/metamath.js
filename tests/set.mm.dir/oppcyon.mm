include "coppc.mm"
include "cfv.mm"
include "cop.mm"
include "ccurf.mm"
include "co.mm"
include "chof.mm"
include "chomf.mm"
include "wceq.mm"
include "2oppchomf.mm"
include "a1i.mm"
include "ccomf.mm"
include "2oppccomf.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "eqid.mm"
include "hofpropd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "crn.mm"
include "csetc.mm"
include "eqidd.mm"
include "cvv.mm"
include "fvex.mm"
include "rnex.mm"
include "wss.mm"
include "ssid.mm"
include "hofcl.mm"
include "curfpropd.mm"
include "yonval.mm"
include "3eqtr4rd.mm"

theorem oppcyon
  let wph: wff ph
  let cC: class C
  let cM: class M
  let cO: class O
  let cY: class Y
  assume oppcyon.o: |- O = ( oppCat ` C )
  assume oppcyon.y: |- Y = ( Yon ` O )
  assume oppcyon.m: |- M = ( HomF ` C )
  assume oppcyon.c: |- ( ph -> C e. Cat )


  assert |- ( ph -> Y = ( <. O , C >. curryF M ) )

  proof
    wph
    cO
    cO
    coppc
    cfv
    #
    cop
    #
    cM
    ccurf
    co
    @1
    @0
    chof
    cfv
    #
    ccurf
    co
    cO
    cC
    cop
    cM
    ccurf
    co
    cY
    wph
    cM
    @2
    @1
    ccurf
    wph
    cM
    cC
    chof
    cfv
    @2
    oppcyon.m
    wph
    cC
    @0
    cC
    chomf
    cfv
    #
    @0
    chomf
    cfv
    wceq
    wph
    cC
    cO
    oppcyon.o
    2oppchomf
    a1i
    #
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
    oppcyon.o
    2oppccomf
    a1i
    #
    oppcyon.c
    wph
    cO
    ccat
    wcel
    #
    @0
    ccat
    wcel
    wph
    cC
    ccat
    wcel
    @6
    oppcyon.c
    cC
    cO
    oppcyon.o
    oppccat
    syl
    #
    cO
    @0
    @0
    eqid
    #
    oppccat
    syl
    #
    hofpropd
    syl5eq
    oveq2d
    wph
    cO
    cO
    cC
    @0
    @3
    crn
    #
    csetc
    cfv
    #
    cM
    wph
    cO
    chomf
    cfv
    eqidd
    wph
    cO
    ccomf
    cfv
    eqidd
    @4
    @5
    @7
    @7
    oppcyon.c
    @9
    wph
    cC
    @11
    @10
    cM
    cO
    cvv
    oppcyon.m
    oppcyon.o
    @11
    eqid
    oppcyon.c
    @10
    cvv
    wcel
    wph
    @3
    cC
    chomf
    fvex
    rnex
    a1i
    @10
    @10
    wss
    wph
    @10
    ssid
    a1i
    hofcl
    curfpropd
    wph
    cO
    @2
    @0
    cY
    oppcyon.y
    @7
    @8
    @2
    eqid
    yonval
    3eqtr4rd
end
