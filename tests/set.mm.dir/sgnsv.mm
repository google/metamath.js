include "wcel.mm"
include "csgns.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "c0g.mm"
include "cplt.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "ifbid.mm"
include "ifbieq2d.mm"
include "mpteq12dva.mm"
include "df-sgns.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "syl5eq.mm"

theorem sgnsv
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cV: class V
  let c.0: class .0.
  let vr: setvar r
  let cX: class X
  assume sgnsval.b: |- B = ( Base ` R )
  assume sgnsval.0: |- .0. = ( 0g ` R )
  assume sgnsval.l: |- .< = ( lt ` R )
  assume sgnsval.s: |- S = ( sgns ` R )

  disjoint .0. x
  disjoint .< x
  disjoint B x
  disjoint R x
  disjoint V x
  disjoint r x
  disjoint .0. r
  disjoint .< r
  disjoint B r
  disjoint R r
  disjoint X x
  assert |- ( R e. V -> S = ( x e. B |-> if ( x = .0. , 0 , if ( .0. .< x , 1 , -u 1 ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cR
    csgns
    cfv
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
    @2
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
    cmpt
    #
    sgnsval.s
    @0
    cR
    cvv
    wcel
    @1
    @8
    wceq
    cR
    cV
    elex
    vr
    cR
    vx
    vr
    cv
    #
    cbs
    cfv
    #
    @2
    @9
    c0g
    cfv
    #
    wceq
    #
    cc0
    @11
    @2
    @9
    cplt
    cfv
    #
    wbr
    #
    c1
    @5
    cif
    #
    cif
    #
    cmpt
    @8
    cvv
    csgns
    @9
    cR
    wceq
    #
    vx
    @10
    @16
    cB
    @7
    @17
    @10
    cR
    cbs
    cfv
    cB
    @9
    cR
    cbs
    fveq2
    sgnsval.b
    syl6eqr
    @17
    @2
    @10
    wcel
    #
    wa
    #
    @12
    @3
    @15
    @6
    cc0
    @19
    @11
    c.0
    @2
    @17
    @11
    c.0
    wceq
    @18
    @17
    @11
    cR
    c0g
    cfv
    c.0
    @9
    cR
    c0g
    fveq2
    sgnsval.0
    syl6eqr
    adantr
    #
    eqeq2d
    @19
    @14
    @4
    c1
    @5
    @19
    @11
    c.0
    @2
    @2
    @13
    c.lt
    @20
    @17
    @13
    c.lt
    wceq
    @18
    @17
    @13
    cR
    cplt
    cfv
    c.lt
    @9
    cR
    cplt
    fveq2
    sgnsval.l
    syl6eqr
    adantr
    @19
    @2
    eqidd
    breq123d
    ifbid
    ifbieq2d
    mpteq12dva
    vx
    vr
    df-sgns
    vx
    @10
    @16
    @9
    cbs
    fvex
    mptex
    fvmpt3i
    syl
    syl5eq
end
