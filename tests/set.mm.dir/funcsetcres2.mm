include "cfunc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "chomf.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "ccat.mm"
include "eqidd.mm"
include "ccomf.mm"
include "cress.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "setccat.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "setcbas.mm"
include "sseqtrd.mm"
include "fullresc.mm"
include "simpld.mm"
include "resssetc.mm"
include "eqtr3d.mm"
include "simprd.mm"
include "funcrcl.mm"
include "adantl.mm"
include "fullsubc.mm"
include "subccat.mm"
include "funcpropd.mm"
include "csubc.mm"
include "funcres2.mm"
include "eqsstr3d.mm"
include "simpr.mm"
include "sseldd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem funcsetcres2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cE: class E
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume resssetc.c: |- C = ( SetCat ` U )
  assume resssetc.d: |- D = ( SetCat ` V )
  assume resssetc.1: |- ( ph -> U e. W )
  assume resssetc.2: |- ( ph -> V C_ U )


  assert |- ( ph -> ( E Func D ) C_ ( E Func C ) )

  proof
    wph
    vf
    cE
    cD
    cfunc
    co
    #
    cE
    cC
    cfunc
    co
    #
    wph
    vf
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    wph
    @3
    wa
    #
    @0
    @1
    @2
    @4
    @0
    cE
    cC
    cC
    chomf
    cfv
    #
    cV
    cV
    cxp
    cres
    #
    cresc
    co
    #
    cfunc
    co
    #
    @1
    @4
    cE
    cE
    @7
    cD
    ccat
    @4
    cE
    chomf
    cfv
    eqidd
    @4
    cE
    ccomf
    cfv
    eqidd
    @4
    cC
    cV
    cress
    co
    #
    chomf
    cfv
    #
    @7
    chomf
    cfv
    #
    cD
    chomf
    cfv
    #
    @4
    @10
    @11
    wceq
    #
    @9
    ccomf
    cfv
    #
    @7
    ccomf
    cfv
    #
    wceq
    #
    @4
    cC
    cbs
    cfv
    #
    cC
    @9
    cV
    @7
    @5
    @17
    eqid
    #
    @5
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @3
    wph
    cU
    cW
    wcel
    @20
    resssetc.1
    cC
    cU
    cW
    resssetc.c
    setccat
    syl
    adantr
    #
    wph
    cV
    @17
    wss
    @3
    wph
    cV
    cU
    @17
    resssetc.2
    wph
    cC
    cU
    cW
    resssetc.c
    resssetc.1
    setcbas
    sseqtrd
    adantr
    #
    @9
    eqid
    @7
    eqid
    #
    fullresc
    #
    simpld
    @4
    @10
    @12
    wceq
    #
    @14
    cD
    ccomf
    cfv
    #
    wceq
    #
    wph
    @25
    @27
    wa
    @3
    wph
    cC
    cD
    cU
    cV
    cW
    resssetc.c
    resssetc.d
    resssetc.1
    resssetc.2
    resssetc
    adantr
    #
    simpld
    eqtr3d
    @4
    @14
    @15
    @26
    @4
    @13
    @16
    @24
    simprd
    @4
    @25
    @27
    @28
    simprd
    eqtr3d
    @4
    cE
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    @3
    @29
    @30
    wa
    wph
    cE
    cD
    @2
    funcrcl
    adantl
    #
    simpld
    #
    @32
    @4
    cC
    @7
    @6
    @23
    @4
    @17
    cC
    cV
    @5
    @18
    @19
    @21
    @22
    fullsubc
    #
    subccat
    @4
    @29
    @30
    @31
    simprd
    funcpropd
    @4
    @6
    cC
    csubc
    cfv
    wcel
    @8
    @1
    wss
    @33
    cE
    cC
    @6
    funcres2
    syl
    eqsstr3d
    wph
    @3
    simpr
    sseldd
    ex
    ssrdv
end
