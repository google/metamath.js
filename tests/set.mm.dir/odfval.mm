include "cod.mm"
include "cfv.mm"
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
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cmg.mm"
include "c0g.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "rabbidv.mm"
include "csbeq1d.mm"
include "mpteq12dv.mm"
include "df-od.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem odfval
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let vi: setvar i
  let cG: class G
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let cA: class A
  let cI: class I
  assume odval.1: |- X = ( Base ` G )
  assume odval.2: |- .x. = ( .g ` G )
  assume odval.3: |- .0. = ( 0g ` G )
  assume odval.4: |- O = ( od ` G )

  disjoint i y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .x. x
  disjoint .x. y
  disjoint .0. x
  disjoint .0. y
  disjoint i x
  disjoint X x
  disjoint g i
  disjoint g y
  disjoint A x
  disjoint A y
  disjoint g x
  disjoint G g
  disjoint .x. g
  disjoint .0. g
  disjoint I i
  disjoint I x
  disjoint X g
  assert |- O = ( x e. X |-> [_ { y e. NN | ( y .x. x ) = .0. } / i ]_ if ( i = (/) , 0 , inf ( i , RR , < ) ) )

  proof
    cO
    cG
    cod
    cfv
    #
    vx
    cX
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
    cc0
    @6
    cr
    clt
    cinf
    cif
    #
    csb
    #
    cmpt
    #
    odval.4
    cG
    cvv
    wcel
    #
    @0
    @9
    wceq
    vg
    cG
    vx
    vg
    cv
    #
    cbs
    cfv
    #
    vi
    @1
    @2
    @11
    cmg
    cfv
    #
    co
    #
    @11
    c0g
    cfv
    #
    wceq
    #
    vy
    cn
    crab
    #
    @7
    csb
    #
    cmpt
    @9
    cvv
    cod
    @11
    cG
    wceq
    #
    vx
    @12
    @18
    cX
    @8
    @19
    @12
    cG
    cbs
    cfv
    #
    cX
    @11
    cG
    cbs
    fveq2
    odval.1
    syl6eqr
    @19
    vi
    @17
    @5
    @7
    @19
    @16
    @4
    vy
    cn
    @19
    @14
    @3
    @15
    c.0
    @19
    @13
    c.x
    @1
    @2
    @19
    @13
    cG
    cmg
    cfv
    c.x
    @11
    cG
    cmg
    fveq2
    odval.2
    syl6eqr
    oveqd
    @19
    @15
    cG
    c0g
    cfv
    c.0
    @11
    cG
    c0g
    fveq2
    odval.3
    syl6eqr
    eqeq12d
    rabbidv
    csbeq1d
    mpteq12dv
    vx
    vg
    vi
    vy
    df-od
    vx
    cX
    @8
    cX
    @20
    cvv
    odval.1
    cG
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    @10
    wn
    #
    @0
    c0
    @9
    cG
    cod
    fvprc
    @21
    @9
    vx
    c0
    @8
    cmpt
    c0
    @21
    vx
    cX
    c0
    @8
    @21
    cX
    @20
    c0
    odval.1
    cG
    cbs
    fvprc
    syl5eq
    mpteq1d
    vx
    @8
    mpt0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
