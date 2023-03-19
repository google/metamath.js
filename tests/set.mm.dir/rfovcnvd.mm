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
include "simprd.mm"

theorem rfovcnvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovcnvf1od.f: |- F = ( A O B )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint W a
  disjoint W x
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> `' F = ( f e. ( ~P B ^m A ) |-> { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } ) )

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
    simprd
end
