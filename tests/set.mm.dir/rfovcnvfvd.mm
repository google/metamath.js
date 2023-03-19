include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "rfovcnvd.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "adantl.mm"
include "simprl.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "sylan.mm"
include "elpwid.mm"
include "sseld.mm"
include "impr.mm"
include "opabex2.mm"
include "fvmptd.mm"

theorem rfovcnvfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovcnvf1od.f: |- F = ( A O B )
  assume rfovcnvfv.g: |- ( ph -> G e. ( ~P B ^m A ) )

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
  disjoint G x
  disjoint G y
  disjoint W a
  disjoint W x
  disjoint a ph
  disjoint b ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint A g
  disjoint a g
  disjoint b g
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint g ph
  assert |- ( ph -> ( `' F ` G ) = { <. x , y >. | ( x e. A /\ y e. ( G ` x ) ) } )

  proof
    wph
    vg
    cG
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @0
    vg
    cv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    @2
    @0
    cG
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cB
    cpw
    #
    cA
    cmap
    co
    #
    cF
    ccnv
    cvv
    wph
    vx
    vy
    cA
    cB
    vg
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
    rfovcnvd
    @3
    cG
    wceq
    #
    @7
    @11
    wceq
    wph
    @14
    @6
    @10
    vx
    vy
    @14
    @5
    @9
    @1
    @14
    @4
    @8
    @2
    @0
    @3
    cG
    fveq1
    eleq2d
    anbi2d
    opabbidv
    adantl
    rfovcnvfv.g
    wph
    @10
    vx
    vy
    cA
    cB
    cV
    cW
    rfovd.a
    rfovd.b
    wph
    @1
    @9
    simprl
    wph
    @1
    @9
    @2
    cB
    wcel
    wph
    @1
    wa
    #
    @8
    cB
    @2
    @15
    @8
    cB
    wph
    cG
    @13
    wcel
    #
    @1
    @8
    @12
    wcel
    rfovcnvfv.g
    @16
    cA
    @12
    @0
    cG
    cG
    @12
    cA
    elmapi
    ffvelrnda
    sylan
    elpwid
    sseld
    impr
    opabex2
    fvmptd
end
