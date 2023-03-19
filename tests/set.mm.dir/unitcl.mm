include "wcel.mm"
include "cur.mm"
include "cfv.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "eqid.mm"
include "isunit.mm"
include "simplbi.mm"
include "dvdsrcl.mm"
include "syl.mm"

theorem unitcl
  let cB: class B
  let cR: class R
  let cU: class U
  let cX: class X
  let vx: setvar x
  assume unitcl.1: |- B = ( Base ` R )
  assume unitcl.2: |- U = ( Unit ` R )


  assert |- ( X e. U -> X e. B )

  proof
    cX
    cU
    wcel
    #
    cX
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    #
    cX
    cB
    wcel
    @0
    @3
    cX
    @1
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @2
    cR
    @4
    cU
    @1
    @5
    cX
    unitcl.2
    @1
    eqid
    @2
    eqid
    #
    @4
    eqid
    @5
    eqid
    isunit
    simplbi
    cB
    @2
    cR
    cX
    @1
    unitcl.1
    @6
    dvdsrcl
    syl
end
