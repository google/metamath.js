include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cdg1.mm"
include "cfv.mm"
include "cco1.mm"
include "cui.mm"
include "simp2.mm"
include "simp3.mm"
include "cbs.mm"
include "c0g.mm"
include "cn0.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "3ad2ant2.mm"
include "crg.mm"
include "drngring.mm"
include "deg1nn0cl.mm"
include "syl3an1.mm"
include "ffvelrnd.mm"
include "deg1ldg.mm"
include "wa.mm"
include "wb.mm"
include "drngunit.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"
include "isuc1p.mm"
include "syl3anbrc.mm"

theorem drnguc1p
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  assume drnguc1p.p: |- P = ( Poly1 ` R )
  assume drnguc1p.b: |- B = ( Base ` P )
  assume drnguc1p.z: |- .0. = ( 0g ` P )
  assume drnguc1p.c: |- C = ( Unic1p ` R )


  assert |- ( ( R e. DivRing /\ F e. B /\ F =/= .0. ) -> F e. C )

  proof
    cR
    cdr
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    w3a
    #
    @1
    @2
    cF
    cR
    cdg1
    cfv
    #
    cfv
    #
    cF
    cco1
    cfv
    #
    cfv
    #
    cR
    cui
    cfv
    #
    wcel
    #
    cF
    cC
    wcel
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @9
    @7
    cR
    cbs
    cfv
    #
    wcel
    #
    @7
    cR
    c0g
    cfv
    #
    wne
    #
    @3
    cn0
    @10
    @5
    @6
    @1
    @0
    cn0
    @10
    @6
    wf
    @2
    @6
    cB
    cP
    cR
    cF
    @10
    @6
    eqid
    #
    drnguc1p.b
    drnguc1p.p
    @10
    eqid
    #
    coe1f
    3ad2ant2
    @0
    cR
    crg
    wcel
    #
    @1
    @2
    @5
    cn0
    wcel
    cR
    drngring
    #
    cB
    @4
    cP
    cR
    cF
    c.0
    @4
    eqid
    #
    drnguc1p.p
    drnguc1p.z
    drnguc1p.b
    deg1nn0cl
    syl3an1
    ffvelrnd
    @0
    @16
    @1
    @2
    @13
    @17
    @6
    cB
    @4
    cP
    cR
    cF
    @12
    c.0
    @18
    drnguc1p.p
    drnguc1p.z
    drnguc1p.b
    @12
    eqid
    #
    @14
    deg1ldg
    syl3an1
    @0
    @1
    @9
    @11
    @13
    wa
    wb
    @2
    @10
    cR
    @8
    @7
    @12
    @15
    @8
    eqid
    #
    @19
    drngunit
    3ad2ant1
    mpbir2and
    cB
    cC
    @4
    cP
    cR
    @8
    cF
    c.0
    drnguc1p.p
    drnguc1p.b
    drnguc1p.z
    @18
    drnguc1p.c
    @20
    isuc1p
    syl3anbrc
end
