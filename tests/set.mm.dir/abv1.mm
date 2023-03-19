include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "c1.mm"
include "wceq.mm"
include "cdr.mm"
include "id.mm"
include "eqid.mm"
include "drngunz.mm"
include "abv1z.mm"
include "syl2anr.mm"

theorem abv1
  let cA: class A
  let cR: class R
  let c.1: class .1.
  let cF: class F
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abv1.p: |- .1. = ( 1r ` R )


  assert |- ( ( R e. DivRing /\ F e. A ) -> ( F ` .1. ) = 1 )

  proof
    cF
    cA
    wcel
    #
    @0
    c.1
    cR
    c0g
    cfv
    #
    wne
    c.1
    cF
    cfv
    c1
    wceq
    cR
    cdr
    wcel
    @0
    id
    cR
    c.1
    @1
    @1
    eqid
    #
    abv1.p
    drngunz
    cA
    cR
    c.1
    cF
    @1
    abv0.a
    abv1.p
    @2
    abv1z
    syl2anr
end
