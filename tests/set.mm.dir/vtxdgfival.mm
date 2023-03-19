include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
include "vtxdgval.mm"
include "adantl.mm"
include "cr.mm"
include "cn0.mm"
include "rabfi.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "jca.mm"
include "adantr.mm"
include "rexadd.mm"
include "eqtrd.mm"

theorem vtxdgfival
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  let vu: setvar u
  assume vtxdgval.v: |- V = ( Vtx ` G )
  assume vtxdgval.i: |- I = ( iEdg ` G )
  assume vtxdgval.a: |- A = dom I

  disjoint A x
  disjoint G x
  disjoint U x
  disjoint A u
  disjoint u x
  disjoint G u
  disjoint I u
  disjoint U u
  disjoint V u
  assert |- ( ( A e. Fin /\ U e. V ) -> ( ( VtxDeg ` G ) ` U ) = ( ( # ` { x e. A | U e. ( I ` x ) } ) + ( # ` { x e. A | ( I ` x ) = { U } } ) ) )

  proof
    cA
    cfn
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    cU
    vx
    cv
    cI
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    @4
    cU
    csn
    wceq
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @7
    @10
    caddc
    co
    #
    @1
    @3
    @11
    wceq
    @0
    vx
    cA
    cU
    cG
    cI
    cV
    vtxdgval.v
    vtxdgval.i
    vtxdgval.a
    vtxdgval
    adantl
    @2
    @7
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    wa
    #
    @11
    @12
    wceq
    @0
    @15
    @1
    @0
    @13
    @14
    @0
    @7
    @0
    @6
    cfn
    wcel
    @7
    cn0
    wcel
    @5
    vx
    cA
    rabfi
    @6
    hashcl
    syl
    nn0red
    @0
    @10
    @0
    @9
    cfn
    wcel
    @10
    cn0
    wcel
    @8
    vx
    cA
    rabfi
    @9
    hashcl
    syl
    nn0red
    jca
    adantr
    @7
    @10
    rexadd
    syl
    eqtrd
end
