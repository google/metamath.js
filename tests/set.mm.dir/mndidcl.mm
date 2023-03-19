include "cmnd.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "mndid.mm"
include "mgmidcl.mm"

theorem mndidcl
  let cB: class B
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume mndidcl.b: |- B = ( Base ` G )
  assume mndidcl.o: |- .0. = ( 0g ` G )


  assert |- ( G e. Mnd -> .0. e. B )

  proof
    cG
    cmnd
    wcel
    vy
    cB
    cG
    cplusg
    cfv
    #
    vx
    cG
    c.0
    mndidcl.b
    mndidcl.o
    @0
    eqid
    #
    vy
    vx
    cB
    @0
    cG
    mndidcl.b
    @1
    mndid
    mgmidcl
end
