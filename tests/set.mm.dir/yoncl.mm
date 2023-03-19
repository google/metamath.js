include "cop.mm"
include "chof.mm"
include "cfv.mm"
include "ccurf.mm"
include "co.mm"
include "cfunc.mm"
include "eqid.mm"
include "yonval.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "oppchofcl.mm"
include "curfcl.mm"
include "eqeltrd.mm"

theorem yoncl
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  let cY: class Y
  let vc: setvar c
  let cM: class M
  assume yonval.y: |- Y = ( Yon ` C )
  assume yonval.c: |- ( ph -> C e. Cat )
  assume yonval.o: |- O = ( oppCat ` C )
  assume yoncl.s: |- S = ( SetCat ` U )
  assume yoncl.q: |- Q = ( O FuncCat S )
  assume yoncl.u: |- ( ph -> U e. V )
  assume yoncl.h: |- ( ph -> ran ( Homf ` C ) C_ U )


  assert |- ( ph -> Y e. ( C Func Q ) )

  proof
    wph
    cY
    cC
    cO
    cop
    cO
    chof
    cfv
    #
    ccurf
    co
    #
    cC
    cQ
    cfunc
    co
    wph
    cC
    @0
    cO
    cY
    yonval.y
    yonval.c
    yonval.o
    @0
    eqid
    #
    yonval
    wph
    cC
    cO
    cQ
    cS
    @0
    @1
    @1
    eqid
    yoncl.q
    yonval.c
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    yonval.c
    cC
    cO
    yonval.o
    oppccat
    syl
    wph
    cC
    cS
    cU
    @0
    cO
    cV
    yonval.o
    @2
    yoncl.s
    yonval.c
    yoncl.u
    yoncl.h
    oppchofcl
    curfcl
    eqeltrd
end
