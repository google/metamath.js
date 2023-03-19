include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "elsuppfn.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rexbidv2.mm"

theorem rexsupp
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z

  disjoint F x
  disjoint V x
  disjoint W x
  disjoint X x
  disjoint Z x
  assert |- ( ( F Fn X /\ X e. V /\ Z e. W ) -> ( E. x e. ( F supp Z ) ph <-> E. x e. X ( ( F ` x ) =/= Z /\ ph ) ) )

  proof
    cF
    cX
    wfn
    cX
    cV
    wcel
    cZ
    cW
    wcel
    w3a
    #
    wph
    vx
    cv
    #
    cF
    cfv
    cZ
    wne
    #
    wph
    wa
    #
    vx
    cF
    cZ
    csupp
    co
    #
    cX
    @0
    @1
    @4
    wcel
    #
    wph
    wa
    @1
    cX
    wcel
    #
    @2
    wa
    #
    wph
    wa
    @6
    @3
    wa
    @0
    @5
    @7
    wph
    @1
    cF
    cV
    cW
    cX
    cZ
    elsuppfn
    anbi1d
    @6
    @2
    wph
    anass
    syl6bb
    rexbidv2
end
