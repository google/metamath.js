include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cspthson.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksnon.mm"
include "crab.mm"
include "cmpt2.mm"
include "cwwspthsnon.mm"
include "wceq.mm"
include "df-wspthsnon.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "oveq12.mm"
include "oveqd.mm"
include "wb.mm"
include "breqd.mm"
include "exbidv.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "simpl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "ovmpt2d.mm"

theorem wspthsnon
  let vw: setvar w
  let cU: class U
  let vf: setvar f
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
  disjoint G f
  disjoint a f
  disjoint b f
  disjoint f w
  disjoint N f
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
  disjoint f g
  disjoint f n
  assert |- ( ( N e. NN0 /\ G e. U ) -> ( N WSPathsNOn G ) = ( a e. V , b e. V |-> { w e. ( a ( N WWalksNOn G ) b ) | E. f f ( a ( SPathsOn ` G ) b ) w } ) )

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
    vf
    cv
    #
    vw
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    @3
    cspthson
    cfv
    #
    co
    #
    wbr
    #
    vf
    wex
    #
    vw
    @7
    @8
    vn
    cv
    #
    @3
    cwwlksnon
    co
    #
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
    @5
    @6
    @7
    @8
    cG
    cspthson
    cfv
    #
    co
    #
    wbr
    #
    vf
    wex
    #
    vw
    @7
    @8
    cN
    cG
    cwwlksnon
    co
    #
    co
    #
    crab
    #
    cmpt2
    #
    cwwspthsnon
    cvv
    cwwspthsnon
    vn
    vg
    cn0
    cvv
    @17
    cmpt2
    wceq
    @2
    vw
    vf
    vg
    vn
    va
    vb
    df-wspthsnon
    a1i
    @13
    cN
    wceq
    #
    @3
    cG
    wceq
    #
    wa
    #
    @17
    @25
    wceq
    @2
    @28
    va
    vb
    @4
    @4
    @16
    cV
    cV
    @24
    @27
    @4
    cV
    wceq
    @26
    @27
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
    @30
    @28
    @12
    @21
    vw
    @15
    @23
    @28
    @14
    @22
    @7
    @8
    @13
    cN
    @3
    cG
    cwwlksnon
    oveq12
    oveqd
    @28
    @11
    @20
    vf
    @27
    @11
    @20
    wb
    @26
    @27
    @10
    @19
    @5
    @6
    @27
    @9
    @18
    @7
    @8
    @3
    cG
    cspthson
    fveq2
    oveqd
    breqd
    adantl
    exbidv
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
    @25
    cvv
    wcel
    @2
    va
    vb
    cV
    cV
    @24
    cV
    @29
    cvv
    wwlksnon.v
    cG
    cvtx
    fvex
    eqeltri
    #
    @31
    mpt2ex
    a1i
    ovmpt2d
end
