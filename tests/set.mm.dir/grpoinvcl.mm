include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cgi.mm"
include "wceq.mm"
include "crio.mm"
include "eqid.mm"
include "grpoinvval.mm"
include "wreu.mm"
include "grpoinveu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem grpoinvcl
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let vy: setvar y
  assume grpinvcl.1: |- X = ran G
  assume grpinvcl.2: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` A ) e. X )

  proof
    cG
    cgr
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cN
    cfv
    vy
    cv
    cA
    cG
    co
    cG
    cgi
    cfv
    #
    wceq
    #
    vy
    cX
    crio
    #
    cX
    vy
    cA
    @1
    cG
    cN
    cX
    grpinvcl.1
    @1
    eqid
    #
    grpinvcl.2
    grpoinvval
    @0
    @2
    vy
    cX
    wreu
    @3
    cX
    wcel
    vy
    cA
    @1
    cG
    cX
    grpinvcl.1
    @4
    grpoinveu
    @2
    vy
    cX
    riotacl
    syl
    eqeltrd
end
