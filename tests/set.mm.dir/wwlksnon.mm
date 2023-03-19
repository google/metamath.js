include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cmpt2.mm"
include "cwwlksnon.mm"
include "df-wwlksnon.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "oveq12.mm"
include "wb.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "simpl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "ovmpt2d.mm"

theorem wwlksnon
  let vw: setvar w
  let cU: class U
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
  assume wwlksnon.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint G w
  disjoint a b
  disjoint a w
  disjoint b w
  disjoint N a
  disjoint N b
  disjoint N w
  disjoint V a
  disjoint V b
  disjoint G g
  disjoint G n
  disjoint a g
  disjoint a n
  disjoint b g
  disjoint b n
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N g
  disjoint N n
  disjoint U g
  disjoint U n
  disjoint V g
  disjoint V n
  assert |- ( ( N e. NN0 /\ G e. U ) -> ( N WWalksNOn G ) = ( a e. V , b e. V |-> { w e. ( N WWalksN G ) | ( ( w ` 0 ) = a /\ ( w ` N ) = b ) } ) )

  proof
    cN
    cn0
    wcel
    #
    cG
    cU
    wcel
    #
    wa
    #
    vn
    vg
    cN
    cG
    cn0
    cvv
    va
    vb
    vg
    cv
    #
    cvtx
    cfv
    #
    @4
    cc0
    vw
    cv
    #
    cfv
    va
    cv
    wceq
    #
    vn
    cv
    #
    @5
    cfv
    #
    vb
    cv
    #
    wceq
    #
    wa
    #
    vw
    @7
    @3
    cwwlksn
    co
    #
    crab
    #
    cmpt2
    #
    va
    vb
    cV
    cV
    @6
    cN
    @5
    cfv
    #
    @9
    wceq
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    cmpt2
    #
    cwwlksnon
    cvv
    cwwlksnon
    vn
    vg
    cn0
    cvv
    @14
    cmpt2
    wceq
    @2
    vw
    vg
    vn
    va
    vb
    df-wwlksnon
    a1i
    @7
    cN
    wceq
    #
    @3
    cG
    wceq
    #
    wa
    #
    @14
    @20
    wceq
    @2
    @23
    va
    vb
    @4
    @4
    @13
    cV
    cV
    @19
    @22
    @4
    cV
    wceq
    @21
    @22
    @4
    cG
    cvtx
    cfv
    #
    cV
    @3
    cG
    cvtx
    fveq2
    wwlksnon.v
    syl6eqr
    adantl
    #
    @25
    @23
    @11
    @17
    vw
    @12
    @18
    @7
    cN
    @3
    cG
    cwwlksn
    oveq12
    @21
    @11
    @17
    wb
    @22
    @21
    @10
    @16
    @6
    @21
    @8
    @15
    @9
    @7
    cN
    @5
    fveq2
    eqeq1d
    anbi2d
    adantr
    rabeqbidv
    mpt2eq123dv
    adantl
    @0
    @1
    simpl
    @1
    cG
    cvv
    wcel
    @0
    cG
    cU
    elex
    adantl
    @20
    cvv
    wcel
    @2
    va
    vb
    cV
    cV
    @19
    cV
    @24
    cvv
    wwlksnon.v
    cG
    cvtx
    fvex
    eqeltri
    #
    @26
    mpt2ex
    a1i
    ovmpt2d
end
