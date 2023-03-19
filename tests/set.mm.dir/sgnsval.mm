include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "sgnsv.mm"
include "adantr.mm"
include "eqeq1.mm"
include "breq2.mm"
include "ifbid.mm"
include "ifbieq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "c0ex.mm"
include "a1i.mm"
include "wn.mm"
include "1ex.mm"
include "negex.mm"
include "ifclda.mm"
include "fvmptd.mm"

theorem sgnsval
  let cB: class B
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  assume sgnsval.b: |- B = ( Base ` R )
  assume sgnsval.0: |- .0. = ( 0g ` R )
  assume sgnsval.l: |- .< = ( lt ` R )
  assume sgnsval.s: |- S = ( sgns ` R )


  assert |- ( ( R e. V /\ X e. B ) -> ( S ` X ) = if ( X = .0. , 0 , if ( .0. .< X , 1 , -u 1 ) ) )

  proof
    cR
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vx
    cX
    vx
    cv
    #
    c.0
    wceq
    #
    cc0
    c.0
    @3
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
    cX
    c.0
    wceq
    #
    cc0
    c.0
    cX
    c.lt
    wbr
    #
    c1
    @6
    cif
    #
    cif
    #
    cB
    cS
    cvv
    @0
    cS
    vx
    cB
    @8
    cmpt
    wceq
    @1
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
    adantr
    @3
    cX
    wceq
    #
    @8
    @12
    wceq
    @2
    @13
    @4
    @9
    @7
    @11
    cc0
    @3
    cX
    c.0
    eqeq1
    @13
    @5
    @10
    c1
    @6
    @3
    cX
    c.0
    c.lt
    breq2
    ifbid
    ifbieq2d
    adantl
    @0
    @1
    simpr
    @2
    @9
    cc0
    @11
    cvv
    cc0
    cvv
    wcel
    @2
    @9
    wa
    c0ex
    a1i
    @2
    @9
    wn
    wa
    #
    @10
    c1
    @6
    cvv
    c1
    cvv
    wcel
    @14
    @10
    wa
    1ex
    a1i
    @6
    cvv
    wcel
    @14
    @10
    wn
    wa
    c1
    negex
    a1i
    ifclda
    ifclda
    fvmptd
end
