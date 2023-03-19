include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cvtx.mm"
include "ctrlson.mm"
include "cspths.mm"
include "cspthson.mm"
include "cvv.mm"
include "1vgrex.mm"
include "adantr.mm"
include "simpl.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "copab.mm"
include "wksv.mm"
include "a1i.mm"
include "cpths.mm"
include "spthispth.mm"
include "pthiswlk.mm"
include "syl.mm"
include "adantl.mm"
include "df-spthson.mm"
include "mptmpt2opabovd.mm"

theorem spthson
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume pthsonfval.v: |- V = ( Vtx ` G )

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint A f
  disjoint A p
  disjoint B f
  disjoint B p
  disjoint V f
  disjoint V p
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a p
  disjoint b f
  disjoint b g
  disjoint b p
  disjoint f g
  disjoint g p
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint B a
  disjoint B b
  disjoint B g
  disjoint V a
  disjoint V g
  assert |- ( ( A e. V /\ B e. V ) -> ( A ( SPathsOn ` G ) B ) = { <. f , p >. | ( f ( A ( TrailsOn ` G ) B ) p /\ f ( SPaths ` G ) p ) } )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    vf
    cv
    #
    vp
    cv
    #
    cG
    cwlks
    cfv
    wbr
    #
    cvtx
    cvtx
    ctrlson
    cspths
    vf
    vg
    vp
    cG
    cspthson
    cvv
    cvv
    cA
    cB
    va
    vb
    @0
    cG
    cvv
    wcel
    @1
    cG
    cA
    cV
    pthsonfval.v
    1vgrex
    adantr
    @2
    cA
    cV
    cG
    cvtx
    cfv
    #
    @0
    @1
    simpl
    pthsonfval.v
    syl6eleq
    @2
    cB
    cV
    @6
    @0
    @1
    simpr
    pthsonfval.v
    syl6eleq
    @5
    vf
    vp
    copab
    cvv
    wcel
    @2
    vf
    cG
    vp
    wksv
    a1i
    @3
    @4
    cG
    cspths
    cfv
    wbr
    #
    @5
    @2
    @7
    @3
    @4
    cG
    cpths
    cfv
    wbr
    @5
    @4
    @3
    cG
    spthispth
    @4
    @3
    cG
    pthiswlk
    syl
    adantl
    vf
    vg
    vp
    va
    vb
    df-spthson
    mptmpt2opabovd
end
