include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cdg1.mm"
include "cco1.mm"
include "cui.mm"
include "eqid.mm"
include "isuc1p.mm"
include "simp2bi.mm"

theorem uc1pn0
  let cC: class C
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  assume uc1pn0.p: |- P = ( Poly1 ` R )
  assume uc1pn0.z: |- .0. = ( 0g ` P )
  assume uc1pn0.c: |- C = ( Unic1p ` R )


  assert |- ( F e. C -> F =/= .0. )

  proof
    cF
    cC
    wcel
    cF
    cP
    cbs
    cfv
    #
    wcel
    cF
    c.0
    wne
    cF
    cR
    cdg1
    cfv
    #
    cfv
    cF
    cco1
    cfv
    cfv
    cR
    cui
    cfv
    #
    wcel
    @0
    cC
    @1
    cP
    cR
    @2
    cF
    c.0
    uc1pn0.p
    @0
    eqid
    uc1pn0.z
    @1
    eqid
    uc1pn0.c
    @2
    eqid
    isuc1p
    simp2bi
end
