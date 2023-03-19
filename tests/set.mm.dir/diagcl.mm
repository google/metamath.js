include "cop.mm"
include "c1stf.mm"
include "co.mm"
include "ccurf.mm"
include "cfunc.mm"
include "diagval.mm"
include "eqid.mm"
include "cxpc.mm"
include "1stfcl.mm"
include "curfcl.mm"
include "eqeltrd.mm"

theorem diagcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cL: class L
  let vc: setvar c
  let vd: setvar d
  assume diagval.l: |- L = ( C DiagFunc D )
  assume diagval.c: |- ( ph -> C e. Cat )
  assume diagval.d: |- ( ph -> D e. Cat )
  assume diagcl.q: |- Q = ( D FuncCat C )


  assert |- ( ph -> L e. ( C Func Q ) )

  proof
    wph
    cL
    cC
    cD
    cop
    cC
    cD
    c1stf
    co
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
    cD
    cL
    diagval.l
    diagval.c
    diagval.d
    diagval
    wph
    cC
    cD
    cQ
    cC
    @0
    @1
    @1
    eqid
    diagcl.q
    diagval.c
    diagval.d
    wph
    cC
    cD
    @0
    cC
    cD
    cxpc
    co
    #
    @2
    eqid
    diagval.c
    diagval.d
    @0
    eqid
    1stfcl
    curfcl
    eqeltrd
end
