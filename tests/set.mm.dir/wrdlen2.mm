include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "wceq.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wrdlen2i.mm"
include "wrd2pr2op.mm"
include "opeq2.mm"
include "adantr.mm"
include "adantl.mm"
include "preq12d.mm"
include "sylan9eq.mm"
include "impbid1.mm"

theorem wrdlen2
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W


  assert |- ( ( S e. V /\ T e. V ) -> ( W = { <. 0 , S >. , <. 1 , T >. } <-> ( ( W e. Word V /\ ( # ` W ) = 2 ) /\ ( ( W ` 0 ) = S /\ ( W ` 1 ) = T ) ) ) )

  proof
    cS
    cV
    wcel
    cT
    cV
    wcel
    wa
    cW
    cc0
    cS
    cop
    #
    c1
    cT
    cop
    #
    cpr
    #
    wceq
    cW
    cV
    cword
    wcel
    cW
    chash
    cfv
    c2
    wceq
    wa
    #
    cc0
    cW
    cfv
    #
    cS
    wceq
    #
    c1
    cW
    cfv
    #
    cT
    wceq
    #
    wa
    #
    wa
    cS
    cT
    cV
    cW
    wrdlen2i
    @3
    @8
    cW
    cc0
    @4
    cop
    #
    c1
    @6
    cop
    #
    cpr
    @2
    cV
    cW
    wrd2pr2op
    @8
    @9
    @0
    @10
    @1
    @5
    @9
    @0
    wceq
    @7
    @4
    cS
    cc0
    opeq2
    adantr
    @7
    @10
    @1
    wceq
    @5
    @6
    cT
    c1
    opeq2
    adantl
    preq12d
    sylan9eq
    impbid1
end
