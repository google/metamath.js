include "cvtx.mm"
include "cfv.mm"
include "eqid.mm"
include "eleqtrrd.mm"
include "ciedg.mm"
include "csn.mm"
include "cop.mm"
include "cpr.mm"
include "wceq.mm"
include "dfsn2.mm"
include "a1i.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "uspgr1e.mm"

theorem 1loopgruspgr
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


  assert |- ( ph -> G e. USPGraph )

  proof
    wph
    cA
    cN
    cN
    cG
    cG
    cvtx
    cfv
    #
    cX
    @0
    eqid
    1loopgruspgr.a
    wph
    cN
    cV
    @0
    1loopgruspgr.n
    1loopgruspgr.v
    eleqtrrd
    #
    @1
    wph
    cG
    ciedg
    cfv
    cA
    cN
    csn
    #
    cop
    #
    csn
    cA
    cN
    cN
    cpr
    #
    cop
    #
    csn
    1loopgruspgr.i
    wph
    @3
    @5
    wph
    @2
    @4
    cA
    @2
    @4
    wceq
    wph
    cN
    dfsn2
    a1i
    opeq2d
    sneqd
    eqtrd
    uspgr1e
end
