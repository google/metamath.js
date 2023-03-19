include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cv.mm"
include "wnel.mm"
include "crab.mm"
include "rabfi.mm"
include "syl5eqel.mm"
include "cun.mm"
include "uncom.mm"
include "eqid.mm"
include "elnelun.mm"
include "eqtr2i.mm"
include "fusgredgfi.mm"
include "anim1i.mm"
include "ancomd.mm"
include "unfi.mm"
include "syl.mm"
include "ex.mm"
include "impbid2.mm"

theorem usgrfilem
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vv: setvar v
  assume fusgredgfi.v: |- V = ( Vtx ` G )
  assume fusgredgfi.e: |- E = ( Edg ` G )
  assume usgrfilem.f: |- F = { e e. E | N e/ e }

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint E v
  disjoint G v
  disjoint V v
  assert |- ( ( G e. FinUSGraph /\ N e. V ) -> ( E e. Fin <-> F e. Fin ) )

  proof
    cG
    cfusgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cE
    cfn
    wcel
    #
    cF
    cfn
    wcel
    #
    @1
    cF
    cN
    ve
    cv
    #
    wnel
    #
    ve
    cE
    crab
    cfn
    usgrfilem.f
    @4
    ve
    cE
    rabfi
    syl5eqel
    @0
    @2
    @1
    @0
    @2
    wa
    #
    cE
    cF
    cN
    @3
    wcel
    ve
    cE
    crab
    #
    cun
    #
    cfn
    @7
    @6
    cF
    cun
    cE
    cF
    @6
    uncom
    cE
    cN
    @3
    @6
    cF
    ve
    @6
    eqid
    usgrfilem.f
    elnelun
    eqtr2i
    @5
    @2
    @6
    cfn
    wcel
    #
    wa
    @7
    cfn
    wcel
    @5
    @8
    @2
    @0
    @8
    @2
    ve
    cE
    cG
    cN
    cV
    fusgredgfi.v
    fusgredgfi.e
    fusgredgfi
    anim1i
    ancomd
    cF
    @6
    unfi
    syl
    syl5eqel
    ex
    impbid2
end
