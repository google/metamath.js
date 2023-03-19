include "cminusg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cplusg.mm"
include "c0g.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "df-minusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "mpt0.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem grpinvfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let c.0: class .0.
  let vg: setvar g
  let cX: class X
  assume grpinvval.b: |- B = ( Base ` G )
  assume grpinvval.p: |- .+ = ( +g ` G )
  assume grpinvval.o: |- .0. = ( 0g ` G )
  assume grpinvval.n: |- N = ( invg ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint .0. x
  disjoint .+ x
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint .0. g
  disjoint .+ g
  disjoint X x
  disjoint X y
  assert |- N = ( x e. B |-> ( iota_ y e. B ( y .+ x ) = .0. ) )

  proof
    cN
    cG
    cminusg
    cfv
    #
    vx
    cB
    vy
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    crio
    #
    cmpt
    #
    grpinvval.n
    cG
    cvv
    wcel
    #
    @0
    @6
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
    @1
    @2
    @8
    cplusg
    cfv
    #
    co
    #
    @8
    c0g
    cfv
    #
    wceq
    #
    vy
    @9
    crio
    #
    cmpt
    @6
    cvv
    cminusg
    @8
    cG
    wceq
    #
    vx
    @9
    @14
    cB
    @5
    @15
    @9
    cG
    cbs
    cfv
    #
    cB
    @8
    cG
    cbs
    fveq2
    grpinvval.b
    syl6eqr
    #
    @15
    @13
    @4
    vy
    @9
    cB
    @17
    @15
    @11
    @3
    @12
    c.0
    @15
    @10
    c.pl
    @1
    @2
    @15
    @10
    cG
    cplusg
    cfv
    c.pl
    @8
    cG
    cplusg
    fveq2
    grpinvval.p
    syl6eqr
    oveqd
    @15
    @12
    cG
    c0g
    cfv
    c.0
    @8
    cG
    c0g
    fveq2
    grpinvval.o
    syl6eqr
    eqeq12d
    riotaeqbidv
    mpteq12dv
    vx
    vy
    vg
    df-minusg
    vx
    cB
    @5
    cB
    @16
    cvv
    grpinvval.b
    cG
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    @7
    wn
    #
    @0
    vx
    c0
    @5
    cmpt
    #
    @6
    @18
    @0
    c0
    @19
    cG
    cminusg
    fvprc
    vx
    @5
    mpt0
    syl6eqr
    @18
    vx
    cB
    c0
    @5
    @18
    cB
    @16
    c0
    grpinvval.b
    cG
    cbs
    fvprc
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end
