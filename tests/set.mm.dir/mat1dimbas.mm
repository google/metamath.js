include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylbb2.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "eqeltri.mm"
include "simp3.mm"
include "opthg.mm"
include "sylancr.mm"
include "sneqbg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "biantrur.mm"
include "3bitr4g.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "mat1dimelbas.mm"
include "3adant3.mm"

theorem mat1dimbas
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cO: class O
  let cV: class V
  let cX: class X
  let vr: setvar r
  let cM: class M
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.


  assert |- ( ( R e. Ring /\ E e. V /\ X e. B ) -> { <. O , X >. } e. ( Base ` A ) )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cO
    cX
    cop
    #
    csn
    #
    cA
    cbs
    cfv
    wcel
    #
    @5
    cO
    vr
    cv
    #
    cop
    #
    csn
    wceq
    #
    vr
    cB
    wrex
    #
    @3
    @10
    cX
    @7
    wceq
    #
    vr
    cB
    wrex
    #
    @2
    @0
    @12
    @1
    @2
    @7
    cX
    wceq
    #
    vr
    cB
    wrex
    @12
    vr
    cX
    cB
    risset
    @11
    @13
    vr
    cB
    cX
    @7
    eqcom
    rexbii
    sylbb2
    3ad2ant3
    @3
    @9
    @11
    vr
    cB
    @3
    @4
    @8
    wceq
    #
    cO
    cO
    wceq
    #
    @11
    wa
    #
    @9
    @11
    @3
    cO
    cvv
    wcel
    @2
    @14
    @16
    wb
    cO
    cE
    cE
    cop
    cvv
    mat1dim.o
    cE
    cE
    opex
    eqeltri
    @0
    @1
    @2
    simp3
    cO
    cX
    cO
    @7
    cvv
    cB
    opthg
    sylancr
    @4
    cvv
    wcel
    @9
    @14
    wb
    cO
    cX
    opex
    @4
    @8
    cvv
    sneqbg
    ax-mp
    @15
    @11
    cO
    eqid
    biantrur
    3bitr4g
    rexbidv
    mpbird
    @0
    @1
    @6
    @10
    wb
    @2
    cA
    cB
    cR
    cE
    @5
    cO
    cV
    vr
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimelbas
    3adant3
    mpbird
end
