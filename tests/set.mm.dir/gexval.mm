include "wcel.mm"
include "cgex.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "cbs.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "csb.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-gex.mm"
include "a1i.mm"
include "wa.mm"
include "nnex.mm"
include "rabex.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "eqeq1d.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "csbied.mm"
include "elex.mm"
include "c0ex.mm"
include "ltso.mm"
include "infex.mm"
include "ifex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem gexval
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vi: setvar i
  assume gexval.1: |- X = ( Base ` G )
  assume gexval.2: |- .x. = ( .g ` G )
  assume gexval.3: |- .0. = ( 0g ` G )
  assume gexval.4: |- E = ( gEx ` G )
  assume gexval.i: |- I = { y e. NN | A. x e. X ( y .x. x ) = .0. }

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint V y
  disjoint .x. x
  disjoint .x. y
  disjoint X x
  disjoint g i
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint i x
  disjoint i y
  disjoint G i
  disjoint I g
  disjoint I i
  disjoint V g
  disjoint V i
  assert |- ( G e. V -> E = if ( I = (/) , 0 , inf ( I , RR , < ) ) )

  proof
    cG
    cV
    wcel
    #
    cE
    cG
    cgex
    cfv
    cI
    c0
    wceq
    #
    cc0
    cI
    cr
    clt
    cinf
    #
    cif
    #
    gexval.4
    @0
    vg
    cG
    vi
    vy
    cv
    #
    vx
    cv
    #
    vg
    cv
    #
    cmg
    cfv
    #
    co
    #
    @6
    c0g
    cfv
    #
    wceq
    #
    vx
    @6
    cbs
    cfv
    #
    wral
    #
    vy
    cn
    crab
    #
    vi
    cv
    #
    c0
    wceq
    #
    cc0
    @14
    cr
    clt
    cinf
    #
    cif
    #
    csb
    #
    @3
    cvv
    cgex
    cvv
    cgex
    vg
    cvv
    @18
    cmpt
    wceq
    @0
    vx
    vg
    vi
    vy
    df-gex
    a1i
    @0
    @6
    cG
    wceq
    #
    wa
    #
    vi
    @13
    @17
    @3
    cvv
    @13
    cvv
    wcel
    @20
    @12
    vy
    cn
    nnex
    rabex
    a1i
    @20
    @14
    @13
    wceq
    #
    wa
    #
    @15
    @1
    @16
    @2
    cc0
    @22
    @14
    cI
    c0
    @20
    @21
    @14
    cI
    wceq
    @20
    @13
    cI
    @14
    @20
    @13
    @4
    @5
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    vy
    cn
    crab
    cI
    @20
    @12
    @25
    vy
    cn
    @20
    @10
    @24
    vx
    @11
    cX
    @20
    @11
    cG
    cbs
    cfv
    cX
    @20
    @6
    cG
    cbs
    @0
    @19
    simpr
    #
    fveq2d
    gexval.1
    syl6eqr
    @20
    @8
    @23
    @9
    c.0
    @20
    @7
    c.x
    @4
    @5
    @20
    @7
    cG
    cmg
    cfv
    c.x
    @20
    @6
    cG
    cmg
    @26
    fveq2d
    gexval.2
    syl6eqr
    oveqd
    @20
    @9
    cG
    c0g
    cfv
    c.0
    @20
    @6
    cG
    c0g
    @26
    fveq2d
    gexval.3
    syl6eqr
    eqeq12d
    raleqbidv
    rabbidv
    gexval.i
    syl6eqr
    eqeq2d
    biimpa
    #
    eqeq1d
    @22
    cr
    @14
    cI
    clt
    @27
    infeq1d
    ifbieq2d
    csbied
    cG
    cV
    elex
    @3
    cvv
    wcel
    @0
    @1
    cc0
    @2
    c0ex
    cr
    cI
    clt
    ltso
    infex
    ifex
    a1i
    fvmptd
    syl5eq
end
