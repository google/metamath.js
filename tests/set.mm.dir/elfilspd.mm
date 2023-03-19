include "cima.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cfn.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "ellspd.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "adantr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "biantrurd.mm"
include "rexbidva.mm"
include "bitr4d.mm"

theorem elfilspd
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  assume ellspd.n: |- N = ( LSpan ` M )
  assume ellspd.v: |- B = ( Base ` M )
  assume ellspd.k: |- K = ( Base ` S )
  assume ellspd.s: |- S = ( Scalar ` M )
  assume ellspd.z: |- .0. = ( 0g ` S )
  assume ellspd.t: |- .x. = ( .s ` M )
  assume elfilspd.f: |- ( ph -> F : I --> B )
  assume elfilspd.m: |- ( ph -> M e. LMod )
  assume elfilspd.i: |- ( ph -> I e. Fin )

  disjoint M f
  disjoint B f
  disjoint N f
  disjoint K f
  disjoint S f
  disjoint .0. f
  disjoint .x. f
  disjoint F f
  disjoint I f
  disjoint X f
  disjoint f ph
  disjoint M a
  disjoint a f
  disjoint B a
  disjoint N a
  disjoint K a
  disjoint S a
  disjoint .0. a
  disjoint .x. a
  disjoint F a
  disjoint I a
  disjoint X a
  disjoint a ph
  assert |- ( ph -> ( X e. ( N ` ( F " I ) ) <-> E. f e. ( K ^m I ) X = ( M gsum ( f oF .x. F ) ) ) )

  proof
    wph
    cX
    cF
    cI
    cima
    cN
    cfv
    wcel
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    cX
    cM
    @0
    cF
    c.x
    cof
    co
    cgsu
    co
    wceq
    #
    wa
    #
    vf
    cK
    cI
    cmap
    co
    #
    wrex
    @2
    vf
    @4
    wrex
    wph
    cB
    cS
    c.x
    vf
    cF
    cI
    cK
    cM
    cN
    cX
    c.0
    ellspd.n
    ellspd.v
    ellspd.k
    ellspd.s
    ellspd.z
    ellspd.t
    elfilspd.f
    elfilspd.m
    wph
    cI
    cfn
    wcel
    #
    cI
    cvv
    wcel
    elfilspd.i
    cI
    cfn
    elex
    syl
    ellspd
    wph
    @2
    @3
    vf
    @4
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @1
    @2
    @7
    cI
    cK
    @0
    cvv
    c.0
    @6
    cI
    cK
    @0
    wf
    wph
    @0
    cK
    cI
    elmapi
    adantl
    wph
    @5
    @6
    elfilspd.i
    adantr
    c.0
    cvv
    wcel
    @7
    c.0
    cS
    c0g
    cfv
    cvv
    ellspd.z
    cS
    c0g
    fvex
    eqeltri
    a1i
    fdmfifsupp
    biantrurd
    rexbidva
    bitr4d
end
