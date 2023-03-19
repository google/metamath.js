include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cvv.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "cfn.mm"
include "cedg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabexg.mm"
include "mp1i.mm"
include "cusgr.mm"
include "isfusgr.mm"
include "hashcl.mm"
include "adantl.mm"
include "sylbi.mm"
include "adantr.mm"
include "fusgrusgr.mm"
include "usgredgleord.mm"
include "sylan.mm"
include "hashbnd.mm"
include "syl3anc.mm"

theorem fusgredgfi
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  assume fusgredgfi.v: |- V = ( Vtx ` G )
  assume fusgredgfi.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  assert |- ( ( G e. FinUSGraph /\ N e. V ) -> { e e. E | N e. e } e. Fin )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cN
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    #
    cvv
    wcel
    #
    cV
    chash
    cfv
    #
    cn0
    wcel
    #
    @4
    chash
    cfv
    @6
    cle
    wbr
    #
    @4
    cfn
    wcel
    cE
    cvv
    wcel
    @5
    @2
    cE
    cG
    cedg
    cfv
    cvv
    fusgredgfi.e
    cG
    cedg
    fvex
    eqeltri
    @3
    ve
    cE
    cvv
    rabexg
    mp1i
    @0
    @7
    @1
    @0
    cG
    cusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    wa
    @7
    cG
    cV
    fusgredgfi.v
    isfusgr
    @10
    @7
    @9
    cV
    hashcl
    adantl
    sylbi
    adantr
    @0
    @9
    @1
    @8
    cG
    fusgrusgr
    ve
    cE
    cG
    cN
    cV
    fusgredgfi.v
    fusgredgfi.e
    usgredgleord
    sylan
    @4
    @6
    cvv
    hashbnd
    syl3anc
end
