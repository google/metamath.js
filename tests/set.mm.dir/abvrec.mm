include "cdr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "c1.mm"
include "cr.mm"
include "simplr.mm"
include "simprl.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "simpll.mm"
include "simprr.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "abvne0.mm"
include "cmulr.mm"
include "co.mm"
include "cur.mm"
include "cmul.mm"
include "wceq.mm"
include "eqid.mm"
include "drnginvrr.mm"
include "fveq2d.mm"
include "abvmul.mm"
include "abv1.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "mvllmuld.mm"

theorem abvrec
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cX: class X
  let c.0: class .0.
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abvneg.b: |- B = ( Base ` R )
  assume abvrec.z: |- .0. = ( 0g ` R )
  assume abvrec.p: |- I = ( invr ` R )


  assert |- ( ( ( R e. DivRing /\ F e. A ) /\ ( X e. B /\ X =/= .0. ) ) -> ( F ` ( I ` X ) ) = ( 1 / ( F ` X ) ) )

  proof
    cR
    cdr
    wcel
    #
    cF
    cA
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    wa
    #
    wa
    #
    cX
    cF
    cfv
    #
    cX
    cI
    cfv
    #
    cF
    cfv
    #
    c1
    @6
    @7
    @6
    @1
    @3
    @7
    cr
    wcel
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprl
    #
    cA
    cB
    cR
    cF
    cX
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @6
    @9
    @6
    @1
    @8
    cB
    wcel
    #
    @9
    cr
    wcel
    @10
    @6
    @0
    @3
    @4
    @12
    @0
    @1
    @5
    simpll
    #
    @11
    @2
    @3
    @4
    simprr
    #
    cB
    cR
    cI
    cX
    c.0
    abvneg.b
    abvrec.z
    abvrec.p
    drnginvrcl
    syl3anc
    #
    cA
    cB
    cR
    cF
    @8
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @6
    @1
    @3
    @4
    @7
    cc0
    wne
    @10
    @11
    @14
    cA
    cB
    cR
    cF
    cX
    c.0
    abv0.a
    abvneg.b
    abvrec.z
    abvne0
    syl3anc
    @6
    cX
    @8
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    cR
    cur
    cfv
    #
    cF
    cfv
    #
    @7
    @9
    cmul
    co
    #
    c1
    @6
    @17
    @19
    cF
    @6
    @0
    @3
    @4
    @17
    @19
    wceq
    @13
    @11
    @14
    cB
    cR
    @16
    @19
    cI
    cX
    c.0
    abvneg.b
    abvrec.z
    @16
    eqid
    #
    @19
    eqid
    #
    abvrec.p
    drnginvrr
    syl3anc
    fveq2d
    @6
    @1
    @3
    @12
    @18
    @21
    wceq
    @10
    @11
    @15
    cA
    cB
    cR
    @16
    cF
    cX
    @8
    abv0.a
    abvneg.b
    @22
    abvmul
    syl3anc
    @2
    @20
    c1
    wceq
    @5
    cA
    cR
    @19
    cF
    abv0.a
    @23
    abv1
    adantr
    3eqtr3d
    mvllmuld
end
