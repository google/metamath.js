include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cplusg.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cneg.mm"
include "cminusg.mm"
include "cif.mm"
include "eqid.mm"
include "mulgfval.mm"
include "fvex.mm"
include "ifex.mm"
include "fnmpt2i.mm"

theorem mulgfn
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let vn: setvar n
  let vx: setvar x
  assume mulgfn.b: |- B = ( Base ` G )
  assume mulgfn.t: |- .x. = ( .g ` G )


  assert |- .x. Fn ( ZZ X. B )

  proof
    vn
    vx
    cz
    cB
    vn
    cv
    #
    cc0
    wceq
    #
    cG
    c0g
    cfv
    #
    cc0
    @0
    clt
    wbr
    #
    @0
    cG
    cplusg
    cfv
    #
    cn
    vx
    cv
    csn
    cxp
    c1
    cseq
    #
    cfv
    #
    @0
    cneg
    @5
    cfv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    c.x
    vx
    cB
    @4
    c.x
    vn
    cG
    @8
    @2
    mulgfn.b
    @4
    eqid
    @2
    eqid
    @8
    eqid
    mulgfn.t
    mulgfval
    @1
    @2
    @10
    cG
    c0g
    fvex
    @3
    @6
    @9
    @0
    @5
    fvex
    @7
    @8
    fvex
    ifex
    ifex
    fnmpt2i
end
