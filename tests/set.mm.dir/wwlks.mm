include "cvv.mm"
include "wcel.mm"
include "cwwlks.mm"
include "cfv.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "crab.mm"
include "wceq.mm"
include "cedg.mm"
include "cvtx.mm"
include "cmpt.mm"
include "df-wwlks.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "id.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wrdexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "fvmptd.mm"
include "wn.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "0wrd0.mm"
include "syl6bb.mm"
include "nne.mm"
include "biimpri.mm"
include "intnanrd.mm"
include "syl6bi.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem wwlks
  let vw: setvar w
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume wwlks.v: |- V = ( Vtx ` G )
  assume wwlks.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint G w
  disjoint i w
  disjoint V w
  disjoint E g
  disjoint G g
  disjoint g i
  disjoint g w
  disjoint V g
  assert |- ( WWalks ` G ) = { w e. Word V | ( w =/= (/) /\ A. i e. ( 0 ..^ ( ( # ` w ) - 1 ) ) { ( w ` i ) , ( w ` ( i + 1 ) ) } e. E ) }

  proof
    cG
    cvv
    wcel
    #
    cG
    cwwlks
    cfv
    #
    vw
    cv
    #
    c0
    wne
    #
    vi
    cv
    #
    @2
    cfv
    @4
    c1
    caddc
    co
    @2
    cfv
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @2
    chash
    cfv
    c1
    cmin
    co
    cfzo
    co
    #
    wral
    #
    wa
    #
    vw
    cV
    cword
    #
    crab
    #
    wceq
    @0
    vg
    cG
    @3
    @5
    vg
    cv
    #
    cedg
    cfv
    #
    wcel
    #
    vi
    @7
    wral
    #
    wa
    #
    vw
    @12
    cvtx
    cfv
    #
    cword
    #
    crab
    #
    @11
    cvv
    cwwlks
    cvv
    cwwlks
    vg
    cvv
    @19
    cmpt
    wceq
    @0
    vw
    vg
    vi
    df-wwlks
    a1i
    @12
    cG
    wceq
    #
    @19
    @11
    wceq
    @0
    @20
    @16
    @9
    vw
    @18
    @10
    @20
    @17
    cV
    wceq
    @18
    @10
    wceq
    @20
    @17
    cG
    cvtx
    cfv
    #
    cV
    @12
    cG
    cvtx
    fveq2
    wwlks.v
    syl6eqr
    @17
    cV
    wrdeq
    syl
    @20
    @15
    @8
    @3
    @20
    @14
    @6
    vi
    @7
    @20
    @13
    cE
    @5
    @20
    @13
    cG
    cedg
    cfv
    cE
    @12
    cG
    cedg
    fveq2
    wwlks.e
    syl6eqr
    eleq2d
    ralbidv
    anbi2d
    rabeqbidv
    adantl
    @0
    id
    @0
    cV
    cvv
    wcel
    #
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    @22
    @0
    cV
    @21
    cvv
    wwlks.v
    cG
    cvtx
    fvex
    eqeltri
    a1i
    cV
    cvv
    wrdexg
    @9
    vw
    @10
    cvv
    rabexg
    3syl
    fvmptd
    @0
    wn
    #
    @1
    c0
    @11
    cG
    cwwlks
    fvprc
    @23
    @9
    wn
    #
    vw
    @10
    wral
    @11
    c0
    wceq
    @23
    @24
    vw
    @10
    @23
    @2
    @10
    wcel
    #
    @2
    c0
    wceq
    #
    @24
    @23
    @25
    @2
    c0
    cword
    #
    wcel
    @26
    @23
    @10
    @27
    @2
    @23
    cV
    c0
    wceq
    @10
    @27
    wceq
    @23
    cV
    @21
    c0
    wwlks.v
    cG
    cvtx
    fvprc
    syl5eq
    cV
    c0
    wrdeq
    syl
    eleq2d
    @2
    0wrd0
    syl6bb
    @26
    @3
    @8
    @3
    wn
    @26
    @2
    c0
    nne
    biimpri
    intnanrd
    syl6bi
    ralrimiv
    @9
    vw
    @10
    rabeq0
    sylibr
    eqtr4d
    pm2.61i
end
