include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cmnd.mm"
include "ccmn.mm"
include "wb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "bitrd.mm"
include "df-cmn.mm"
include "elrab2.mm"

theorem iscmn
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let vg: setvar g
  assume iscmn.b: |- B = ( Base ` G )
  assume iscmn.p: |- .+ = ( +g ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint .+ g
  assert |- ( G e. CMnd <-> ( G e. Mnd /\ A. x e. B A. y e. B ( x .+ y ) = ( y .+ x ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    cplusg
    cfv
    #
    co
    #
    @1
    @0
    @3
    co
    #
    wceq
    #
    vy
    @2
    cbs
    cfv
    #
    wral
    #
    vx
    @7
    wral
    #
    @0
    @1
    c.pl
    co
    #
    @1
    @0
    c.pl
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vg
    cG
    cmnd
    ccmn
    @2
    cG
    wceq
    #
    @9
    @6
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @13
    @14
    @7
    cB
    wceq
    @9
    @16
    wb
    @14
    @7
    cG
    cbs
    cfv
    cB
    @2
    cG
    cbs
    fveq2
    iscmn.b
    syl6eqr
    @8
    @15
    vx
    @7
    cB
    @6
    vy
    @7
    cB
    raleq
    raleqbi1dv
    syl
    @14
    @6
    @12
    vx
    vy
    cB
    cB
    @14
    @4
    @10
    @5
    @11
    @14
    @3
    c.pl
    @0
    @1
    @14
    @3
    cG
    cplusg
    cfv
    c.pl
    @2
    cG
    cplusg
    fveq2
    iscmn.p
    syl6eqr
    #
    oveqd
    @14
    @3
    c.pl
    @1
    @0
    @17
    oveqd
    eqeq12d
    2ralbidv
    bitrd
    vg
    vx
    vy
    df-cmn
    elrab2
end
