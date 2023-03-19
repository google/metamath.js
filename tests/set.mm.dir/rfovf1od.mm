include "cxp.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "wceq.mm"
include "rfovcnvf1od.mm"
include "simpld.mm"

theorem rfovf1od
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovcnvf1od.f: |- F = ( A O B )

  disjoint A a
  disjoint A b
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint W a
  disjoint W x
  disjoint a ph
  disjoint b ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint A f
  disjoint a f
  disjoint b f
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint f ph
  assert |- ( ph -> F : ~P ( A X. B ) -1-1-onto-> ( ~P B ^m A ) )

  proof
    wph
    cA
    cB
    cxp
    cpw
    cB
    cpw
    cA
    cmap
    co
    #
    cF
    wf1o
    cF
    ccnv
    vf
    @0
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    @1
    vf
    cv
    cfv
    wcel
    wa
    vx
    vy
    copab
    cmpt
    wceq
    wph
    vx
    vy
    cA
    cB
    vf
    cF
    cO
    cV
    cW
    vr
    va
    vb
    rfovd.rf
    rfovd.a
    rfovd.b
    rfovcnvf1od.f
    rfovcnvf1od
    simpld
end
