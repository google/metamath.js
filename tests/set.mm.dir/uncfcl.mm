include "cevlf.mm"
include "co.mm"
include "c1stf.mm"
include "ccofu.mm"
include "c2ndf.mm"
include "cprf.mm"
include "cxpc.mm"
include "cfunc.mm"
include "uncfval.mm"
include "cfuc.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "1stfcl.mm"
include "cofucl.mm"
include "2ndfcl.mm"
include "prfcl.mm"
include "evlfcl.mm"
include "eqeltrd.mm"

theorem uncfcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume uncfval.g: |- F = ( <" C D E "> uncurryF G )
  assume uncfval.c: |- ( ph -> D e. Cat )
  assume uncfval.d: |- ( ph -> E e. Cat )
  assume uncfval.f: |- ( ph -> G e. ( C Func ( D FuncCat E ) ) )


  assert |- ( ph -> F e. ( ( C Xc. D ) Func E ) )

  proof
    wph
    cF
    cD
    cE
    cevlf
    co
    #
    cG
    cC
    cD
    c1stf
    co
    #
    ccofu
    co
    #
    cC
    cD
    c2ndf
    co
    #
    cprf
    co
    #
    ccofu
    co
    cC
    cD
    cxpc
    co
    #
    cE
    cfunc
    co
    wph
    cC
    cD
    cE
    cF
    cG
    uncfval.g
    uncfval.c
    uncfval.d
    uncfval.f
    uncfval
    wph
    @5
    cD
    cE
    cfuc
    co
    #
    cD
    cxpc
    co
    #
    cE
    @4
    @0
    wph
    @5
    @6
    @4
    @7
    cD
    @2
    @3
    @4
    eqid
    @7
    eqid
    wph
    @5
    cC
    @6
    @1
    cG
    wph
    cC
    cD
    @1
    @5
    @5
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @6
    ccat
    wcel
    #
    wph
    cG
    cC
    @6
    cfunc
    co
    wcel
    @9
    @10
    wa
    uncfval.f
    cC
    @6
    cG
    funcrcl
    syl
    simpld
    #
    uncfval.c
    @1
    eqid
    1stfcl
    uncfval.f
    cofucl
    wph
    cC
    cD
    @3
    @5
    @8
    @11
    uncfval.c
    @3
    eqid
    2ndfcl
    prfcl
    wph
    cD
    cE
    @6
    @0
    @0
    eqid
    @6
    eqid
    uncfval.c
    uncfval.d
    evlfcl
    cofucl
    eqeltrd
end
