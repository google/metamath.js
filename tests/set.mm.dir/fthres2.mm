include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cresc.mm"
include "co.mm"
include "cfth.mm"
include "wrel.mm"
include "relfth.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "cfunc.mm"
include "ccnv.mm"
include "wfun.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "funcres2.mm"
include "ssbrd.mm"
include "anim1d.mm"
include "eqid.mm"
include "isfth.mm"
include "3imtr4g.mm"
include "df-br.mm"
include "3imtr3g.mm"
include "relssdv.mm"

theorem fthres2
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. ( Subcat ` D ) -> ( C Faith ( D |`cat R ) ) C_ ( C Faith D ) )

  proof
    cR
    cD
    csubc
    cfv
    wcel
    #
    vf
    vg
    cC
    cD
    cR
    cresc
    co
    #
    cfth
    co
    #
    cC
    cD
    cfth
    co
    #
    @2
    wrel
    @0
    cC
    @1
    relfth
    a1i
    @0
    vf
    cv
    #
    vg
    cv
    #
    @2
    wbr
    #
    @4
    @5
    @3
    wbr
    #
    @4
    @5
    cop
    #
    @2
    wcel
    @8
    @3
    wcel
    @0
    @4
    @5
    cC
    @1
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    vy
    cv
    @5
    co
    ccnv
    wfun
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @11
    wral
    #
    wa
    @4
    @5
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    @12
    wa
    @6
    @7
    @0
    @10
    @14
    @12
    @0
    @9
    @13
    @4
    @5
    cC
    cD
    cR
    funcres2
    ssbrd
    anim1d
    vx
    vy
    @11
    cC
    @1
    @4
    @5
    @11
    eqid
    #
    isfth
    vx
    vy
    @11
    cC
    cD
    @4
    @5
    @15
    isfth
    3imtr4g
    @4
    @5
    @2
    df-br
    @4
    @5
    @3
    df-br
    3imtr3g
    relssdv
end
