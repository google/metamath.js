include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "wcel.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "dpjidcl.mm"
include "simprd.mm"

theorem dpjid
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let vh: setvar h
  let vk: setvar k
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjid.3: |- ( ph -> A e. ( G DProd S ) )

  disjoint G x
  disjoint P x
  disjoint ph x
  disjoint I x
  disjoint A x
  disjoint S x
  disjoint h k
  disjoint h x
  disjoint .0. h
  disjoint k x
  disjoint .0. k
  disjoint .0. x
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f s
  disjoint f x
  disjoint G f
  disjoint g h
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint G g
  disjoint h i
  disjoint h s
  disjoint G h
  disjoint i k
  disjoint i s
  disjoint i x
  disjoint G i
  disjoint k s
  disjoint G k
  disjoint s x
  disjoint G s
  disjoint P f
  disjoint P h
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint k ph
  disjoint ph s
  disjoint C h
  disjoint I f
  disjoint I g
  disjoint I h
  disjoint I i
  disjoint I k
  disjoint I s
  disjoint Q g
  disjoint Q s
  disjoint Q x
  disjoint W f
  disjoint W k
  disjoint W x
  disjoint X h
  disjoint X x
  disjoint A f
  disjoint A h
  disjoint A k
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S i
  disjoint S k
  disjoint S s
  disjoint Y x
  assert |- ( ph -> A = ( G gsum ( x e. I |-> ( ( P ` x ) ` A ) ) ) )

  proof
    wph
    vx
    cI
    cA
    vx
    cv
    cP
    cfv
    cfv
    cmpt
    #
    vh
    cv
    cG
    c0g
    cfv
    #
    cfsupp
    wbr
    vh
    vi
    cI
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    wcel
    cA
    cG
    @0
    cgsu
    co
    wceq
    wph
    vx
    cA
    cP
    cS
    vh
    vi
    cG
    cI
    @2
    @1
    dpjfval.1
    dpjfval.2
    dpjfval.p
    dpjid.3
    @1
    eqid
    @2
    eqid
    dpjidcl
    simprd
end
