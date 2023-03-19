include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "csb.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "nnex.mm"
include "rabex2.mm"
include "eqeq1.mm"
include "infeq1.mm"
include "ifbieq2d.mm"
include "csbie.mm"
include "syl6eq.mm"
include "odfval.mm"
include "c0ex.mm"
include "ltso.mm"
include "infex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem odval
  let vy: setvar y
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vi: setvar i
  let vx: setvar x
  assume odval.1: |- X = ( Base ` G )
  assume odval.2: |- .x. = ( .g ` G )
  assume odval.3: |- .0. = ( 0g ` G )
  assume odval.4: |- O = ( od ` G )
  assume odval.i: |- I = { y e. NN | ( y .x. A ) = .0. }

  disjoint A y
  disjoint G y
  disjoint .x. y
  disjoint .0. y
  disjoint g i
  disjoint g y
  disjoint i y
  disjoint x y
  disjoint A x
  disjoint g x
  disjoint G g
  disjoint G x
  disjoint .x. g
  disjoint .x. x
  disjoint .0. g
  disjoint .0. x
  disjoint i x
  disjoint I i
  disjoint I x
  disjoint X g
  disjoint X x
  assert |- ( A e. X -> ( O ` A ) = if ( I = (/) , 0 , inf ( I , RR , < ) ) )

  proof
    vx
    cA
    vi
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    c.0
    wceq
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
    @5
    cr
    clt
    cinf
    #
    cif
    #
    csb
    #
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
    cX
    cO
    @1
    cA
    wceq
    #
    @9
    vi
    cI
    @8
    csb
    @12
    @13
    vi
    @4
    cI
    @8
    @13
    @4
    @0
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    vy
    cn
    crab
    cI
    @13
    @3
    @15
    vy
    cn
    @13
    @2
    @14
    c.0
    @1
    cA
    @0
    c.x
    oveq2
    eqeq1d
    rabbidv
    odval.i
    syl6eqr
    csbeq1d
    vi
    cI
    @8
    @12
    @15
    vy
    cn
    cI
    odval.i
    nnex
    rabex2
    @5
    cI
    wceq
    @6
    @10
    @7
    @11
    cc0
    @5
    cI
    c0
    eqeq1
    cr
    @5
    cI
    clt
    infeq1
    ifbieq2d
    csbie
    syl6eq
    vx
    vy
    c.x
    vi
    cG
    cO
    cX
    c.0
    odval.1
    odval.2
    odval.3
    odval.4
    odfval
    @10
    cc0
    @11
    c0ex
    cr
    cI
    clt
    ltso
    infex
    ifex
    fvmpt
end
