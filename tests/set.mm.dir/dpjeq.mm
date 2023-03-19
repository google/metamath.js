include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "dpjidcl.mm"
include "simprd.mm"
include "eqeq1d.mm"
include "simpld.mm"
include "dprdf11.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "mp1i.mm"
include "3bitrd.mm"

theorem dpjeq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cP: class P
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let cQ: class Q
  let cX: class X
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjidcl.3: |- ( ph -> A e. ( G DProd S ) )
  assume dpjidcl.0: |- .0. = ( 0g ` G )
  assume dpjidcl.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dpjeq.c: |- ( ph -> ( x e. I |-> C ) e. W )

  disjoint h x
  disjoint .0. h
  disjoint .0. x
  disjoint h i
  disjoint G h
  disjoint i x
  disjoint G i
  disjoint G x
  disjoint P h
  disjoint P x
  disjoint i ph
  disjoint ph x
  disjoint C h
  disjoint I h
  disjoint I i
  disjoint I x
  disjoint W x
  disjoint A h
  disjoint A x
  disjoint S h
  disjoint S i
  disjoint S x
  disjoint h k
  disjoint k x
  disjoint .0. k
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
  disjoint h s
  disjoint i k
  disjoint i s
  disjoint k s
  disjoint G k
  disjoint s x
  disjoint G s
  disjoint P f
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph s
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I s
  disjoint Q g
  disjoint Q s
  disjoint Q x
  disjoint W f
  disjoint W k
  disjoint X h
  disjoint X x
  disjoint A f
  disjoint A k
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S s
  disjoint Y x
  assert |- ( ph -> ( A = ( G gsum ( x e. I |-> C ) ) <-> A. x e. I ( ( P ` x ) ` A ) = C ) )

  proof
    wph
    cA
    cG
    vx
    cI
    cC
    cmpt
    #
    cgsu
    co
    #
    wceq
    cG
    vx
    cI
    cA
    vx
    cv
    cP
    cfv
    #
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @1
    wceq
    @4
    @0
    wceq
    #
    @3
    cC
    wceq
    vx
    cI
    wral
    #
    wph
    cA
    @5
    @1
    wph
    @4
    cW
    wcel
    #
    cA
    @5
    wceq
    #
    wph
    vx
    cA
    cP
    cS
    vh
    vi
    cG
    cI
    cW
    c.0
    dpjfval.1
    dpjfval.2
    dpjfval.p
    dpjidcl.3
    dpjidcl.0
    dpjidcl.w
    dpjidcl
    #
    simprd
    eqeq1d
    wph
    cS
    vh
    vi
    @4
    cG
    @0
    cI
    cW
    c.0
    dpjidcl.0
    dpjidcl.w
    dpjfval.1
    dpjfval.2
    wph
    @8
    @9
    @10
    simpld
    dpjeq.c
    dprdf11
    @3
    cvv
    wcel
    #
    vx
    cI
    wral
    @6
    @7
    wb
    wph
    @11
    vx
    cI
    cA
    @2
    fvex
    rgenw
    vx
    cI
    @3
    cC
    cvv
    mpteqb
    mp1i
    3bitrd
end
