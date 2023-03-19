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
include "wfn.mm"
include "eqid.mm"
include "funcixp.mm"
include "ixpfn.mm"
include "syl.mm"

theorem funcfn2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume funcfn2.b: |- B = ( Base ` D )
  assume funcfn2.f: |- ( ph -> F ( D Func E ) G )


  assert |- ( ph -> G Fn ( B X. B ) )

  proof
    wph
    cG
    vx
    cB
    cB
    cxp
    #
    vx
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
    #
    cixp
    wcel
    cG
    @0
    wfn
    wph
    vx
    cB
    cD
    cE
    cF
    cG
    @3
    @2
    funcfn2.b
    @3
    eqid
    @2
    eqid
    funcfn2.f
    funcixp
    vx
    @0
    @4
    cG
    ixpfn
    syl
end
