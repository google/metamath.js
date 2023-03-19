include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "ctp.mm"
include "sgnsv.mm"
include "wa.mm"
include "c0ex.mm"
include "tpid2.mm"
include "1ex.mm"
include "tpid3.mm"
include "negex.mm"
include "tpid1.mm"
include "keepel.mm"
include "a1i.mm"
include "fmpt3d.mm"

theorem sgnsf
  let cB: class B
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cV: class V
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  let cX: class X
  assume sgnsval.b: |- B = ( Base ` R )
  assume sgnsval.0: |- .0. = ( 0g ` R )
  assume sgnsval.l: |- .< = ( lt ` R )
  assume sgnsval.s: |- S = ( sgns ` R )


  assert |- ( R e. V -> S : B --> { -u 1 , 0 , 1 } )

  proof
    cR
    cV
    wcel
    #
    vx
    cB
    vx
    cv
    #
    c.0
    wceq
    #
    cc0
    c.0
    @1
    c.lt
    wbr
    #
    c1
    c1
    cneg
    #
    cif
    #
    cif
    #
    @4
    cc0
    c1
    ctp
    #
    cS
    vx
    cB
    cR
    cS
    c.lt
    cV
    c.0
    sgnsval.b
    sgnsval.0
    sgnsval.l
    sgnsval.s
    sgnsv
    @6
    @7
    wcel
    @0
    @1
    cB
    wcel
    wa
    @2
    cc0
    @5
    @7
    @4
    cc0
    c1
    c0ex
    tpid2
    @3
    c1
    @4
    @7
    @4
    cc0
    c1
    1ex
    tpid3
    @4
    cc0
    c1
    c1
    negex
    tpid1
    keepel
    keepel
    a1i
    fmpt3d
end
