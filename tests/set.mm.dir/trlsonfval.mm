include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cvtx.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "ctrlson.mm"
include "cvv.mm"
include "1vgrex.mm"
include "adantr.mm"
include "simpl.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "copab.mm"
include "wksv.mm"
include "a1i.mm"
include "trliswlk.mm"
include "adantl.mm"
include "df-trlson.mm"
include "mptmpt2opabovd.mm"

theorem trlsonfval
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume trlsonfval.v: |- V = ( Vtx ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint G f
  disjoint G p
  disjoint V f
  disjoint V p
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a p
  disjoint b f
  disjoint b g
  disjoint b p
  disjoint f g
  disjoint g p
  disjoint B a
  disjoint B b
  disjoint B g
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint V a
  disjoint V b
  disjoint V g
  assert |- ( ( A e. V /\ B e. V ) -> ( A ( TrailsOn ` G ) B ) = { <. f , p >. | ( f ( A ( WalksOn ` G ) B ) p /\ f ( Trails ` G ) p ) } )

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
    cwlkson
    ctrls
    vf
    vg
    vp
    cG
    ctrlson
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
    trlsonfval.v
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
    trlsonfval.v
    syl6eleq
    @2
    cB
    cV
    @6
    @0
    @1
    simpr
    trlsonfval.v
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
    ctrls
    cfv
    wbr
    @5
    @2
    @4
    @3
    cG
    trliswlk
    adantl
    vf
    vg
    vp
    va
    vb
    df-trlson
    mptmpt2opabovd
end
