include "wcel.mm"
include "cvv.mm"
include "crrh.mm"
include "cfv.mm"
include "cqqh.mm"
include "ccnext.mm"
include "co.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctopn.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "fveq12d.mm"
include "df-rrh.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem rrhval
  let cR: class R
  let cJ: class J
  let cK: class K
  let cV: class V
  let vr: setvar r
  assume rrhval.1: |- J = ( topGen ` ran (,) )
  assume rrhval.2: |- K = ( TopOpen ` R )


  assert |- ( R e. V -> ( RRHom ` R ) = ( ( J CnExt K ) ` ( QQHom ` R ) ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    cR
    crrh
    cfv
    cR
    cqqh
    cfv
    #
    cJ
    cK
    ccnext
    co
    #
    cfv
    #
    wceq
    cR
    cV
    elex
    vr
    cR
    vr
    cv
    #
    cqqh
    cfv
    #
    cioo
    crn
    ctg
    cfv
    #
    @3
    ctopn
    cfv
    #
    ccnext
    co
    #
    cfv
    @2
    cvv
    crrh
    @3
    cR
    wceq
    #
    @4
    @0
    @7
    @1
    @8
    @5
    cJ
    @6
    cK
    ccnext
    @5
    cJ
    wceq
    @8
    cJ
    @5
    rrhval.1
    eqcomi
    a1i
    @8
    @6
    cR
    ctopn
    cfv
    cK
    @3
    cR
    ctopn
    fveq2
    rrhval.2
    syl6eqr
    oveq12d
    @3
    cR
    cqqh
    fveq2
    fveq12d
    vr
    df-rrh
    @0
    @1
    fvex
    fvmpt
    syl
end
