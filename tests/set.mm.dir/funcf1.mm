include "wf.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "chom.mm"
include "co.mm"
include "cmap.mm"
include "cixp.mm"
include "wcel.mm"
include "ccid.mm"
include "wceq.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "cfunc.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "ccat.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "isfunc.mm"
include "mpbid.mm"
include "simp1d.mm"

theorem funcf1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funcf1.b: |- B = ( Base ` D )
  assume funcf1.c: |- C = ( Base ` E )
  assume funcf1.f: |- ( ph -> F ( D Func E ) G )


  assert |- ( ph -> F : B --> C )

  proof
    wph
    cB
    cC
    cF
    wf
    #
    cG
    vz
    cB
    cB
    cxp
    vz
    cv
    #
    c1st
    cfv
    cF
    cfv
    @1
    c2nd
    cfv
    cF
    cfv
    cE
    chom
    cfv
    #
    co
    @1
    cD
    chom
    cfv
    #
    cfv
    cmap
    co
    cixp
    wcel
    #
    vx
    cv
    #
    cD
    ccid
    cfv
    #
    cfv
    @5
    @5
    cG
    co
    cfv
    @5
    cF
    cfv
    #
    cE
    ccid
    cfv
    #
    cfv
    wceq
    vn
    cv
    #
    vm
    cv
    #
    @5
    vy
    cv
    #
    cop
    @1
    cD
    cco
    cfv
    #
    co
    co
    @5
    @1
    cG
    co
    cfv
    @9
    @11
    @1
    cG
    co
    cfv
    @10
    @5
    @11
    cG
    co
    cfv
    @7
    @11
    cF
    cfv
    cop
    @1
    cF
    cfv
    cE
    cco
    cfv
    #
    co
    co
    wceq
    vn
    @11
    @1
    @3
    co
    wral
    vm
    @5
    @11
    @3
    co
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    wa
    vx
    cB
    wral
    #
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    #
    wbr
    #
    @0
    @4
    @14
    w3a
    funcf1.f
    wph
    vx
    vy
    vz
    cB
    cC
    cD
    @12
    @6
    vm
    vn
    cE
    cF
    cG
    @3
    @8
    @2
    @13
    funcf1.b
    funcf1.c
    @3
    eqid
    @2
    eqid
    @6
    eqid
    @8
    eqid
    @12
    eqid
    @13
    eqid
    wph
    cD
    ccat
    wcel
    #
    cE
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    @15
    wcel
    #
    @17
    @18
    wa
    wph
    @16
    @20
    funcf1.f
    cF
    cG
    @15
    df-br
    sylib
    cD
    cE
    @19
    funcrcl
    syl
    #
    simpld
    wph
    @17
    @18
    @21
    simprd
    isfunc
    mpbid
    simp1d
end
