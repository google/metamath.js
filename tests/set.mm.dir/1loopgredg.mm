include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "csn.mm"
include "cop.mm"
include "wceq.mm"
include "edgval.mm"
include "a1i.mm"
include "rneqd.mm"
include "wcel.mm"
include "rnsnopg.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem 1loopgredg
  let wph: wff ph
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  assume 1loopgruspgr.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1loopgruspgr.a: |- ( ph -> A e. X )
  assume 1loopgruspgr.n: |- ( ph -> N e. V )
  assume 1loopgruspgr.i: |- ( ph -> ( iEdg ` G ) = { <. A , { N } >. } )


  assert |- ( ph -> ( Edg ` G ) = { { N } } )

  proof
    wph
    cG
    cedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    cA
    cN
    csn
    #
    cop
    csn
    #
    crn
    #
    @3
    csn
    #
    @0
    @2
    wceq
    wph
    cG
    edgval
    a1i
    wph
    @1
    @4
    1loopgruspgr.i
    rneqd
    wph
    cA
    cX
    wcel
    @5
    @6
    wceq
    1loopgruspgr.a
    cA
    @3
    cX
    rnsnopg
    syl
    3eqtrd
end
