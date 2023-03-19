include "cvv.mm"
include "wcel.mm"
include "cclwwlk.mm"
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
include "clsw.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "wceq.mm"
include "cedg.mm"
include "cvtx.mm"
include "cmpt.mm"
include "df-clwwlk.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
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
include "wa.mm"
include "noel.mm"
include "syl5eq.mm"
include "mtbiri.mm"
include "adantr.mm"
include "intn3an3d.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem clwwlk
  let vw: setvar w
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume clwwlk.v: |- V = ( Vtx ` G )
  assume clwwlk.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint G w
  disjoint i w
  disjoint V w
  disjoint E g
  disjoint G g
  disjoint g i
  disjoint g w
  disjoint V g
  assert |- ( ClWWalks ` G ) = { w e. Word V | ( w =/= (/) /\ A. i e. ( 0 ..^ ( ( # ` w ) - 1 ) ) { ( w ` i ) , ( w ` ( i + 1 ) ) } e. E /\ { ( lastS ` w ) , ( w ` 0 ) } e. E ) }

  proof
    cG
    cvv
    wcel
    #
    cG
    cclwwlk
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
    @2
    clsw
    cfv
    cc0
    @2
    cfv
    cpr
    #
    cE
    wcel
    #
    w3a
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
    @9
    @15
    wcel
    #
    w3a
    #
    vw
    @14
    cvtx
    cfv
    #
    cword
    #
    crab
    #
    @13
    cvv
    cclwwlk
    cvv
    cclwwlk
    vg
    cvv
    @22
    cmpt
    wceq
    @0
    vw
    vg
    vi
    df-clwwlk
    a1i
    @14
    cG
    wceq
    #
    @22
    @13
    wceq
    @0
    @23
    @19
    @11
    vw
    @21
    @12
    @23
    @20
    cV
    wceq
    @21
    @12
    wceq
    @23
    @20
    cG
    cvtx
    cfv
    #
    cV
    @14
    cG
    cvtx
    fveq2
    clwwlk.v
    syl6eqr
    @20
    cV
    wrdeq
    syl
    @23
    @17
    @8
    @18
    @10
    @3
    @23
    @16
    @6
    vi
    @7
    @23
    @15
    cE
    @5
    @23
    @15
    cG
    cedg
    cfv
    #
    cE
    @14
    cG
    cedg
    fveq2
    clwwlk.e
    syl6eqr
    #
    eleq2d
    ralbidv
    @23
    @15
    cE
    @9
    @26
    eleq2d
    3anbi23d
    rabeqbidv
    adantl
    @0
    id
    @0
    cV
    cvv
    wcel
    #
    @12
    cvv
    wcel
    @13
    cvv
    wcel
    @27
    @0
    cV
    @24
    cvv
    clwwlk.v
    cG
    cvtx
    fvex
    eqeltri
    a1i
    cV
    cvv
    wrdexg
    @11
    vw
    @12
    cvv
    rabexg
    3syl
    fvmptd
    @0
    wn
    #
    @1
    c0
    @13
    cG
    cclwwlk
    fvprc
    @28
    @11
    wn
    #
    vw
    @12
    wral
    @13
    c0
    wceq
    @28
    @29
    vw
    @12
    @28
    @2
    @12
    wcel
    #
    wa
    @10
    @3
    @8
    @28
    @10
    wn
    @30
    @28
    @10
    @9
    c0
    wcel
    @9
    noel
    @28
    cE
    c0
    @9
    @28
    cE
    @25
    c0
    clwwlk.e
    cG
    cedg
    fvprc
    syl5eq
    eleq2d
    mtbiri
    adantr
    intn3an3d
    ralrimiva
    @11
    vw
    @12
    rabeq0
    sylibr
    eqtr4d
    pm2.61i
end
