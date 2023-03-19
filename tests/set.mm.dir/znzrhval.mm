include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cfv.mm"
include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "znzrh2.mm"
include "fveq1d.mm"
include "eceq1.mm"
include "eqid.mm"
include "cvv.mm"
include "zring.mm"
include "csn.mm"
include "cqg.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem znzrhval
  let cA: class A
  let c.sm: class .~
  let cS: class S
  let cL: class L
  let cN: class N
  let cY: class Y
  let vx: setvar x
  assume znzrh2.s: |- S = ( RSpan ` ZZring )
  assume znzrh2.r: |- .~ = ( ZZring ~QG ( S ` { N } ) )
  assume znzrh2.y: |- Y = ( Z/nZ ` N )
  assume znzrh2.2: |- L = ( ZRHom ` Y )


  assert |- ( ( N e. NN0 /\ A e. ZZ ) -> ( L ` A ) = [ A ] .~ )

  proof
    cN
    cn0
    wcel
    #
    cA
    cz
    wcel
    cA
    cL
    cfv
    cA
    vx
    cz
    vx
    cv
    #
    c.sm
    cec
    #
    cmpt
    #
    cfv
    cA
    c.sm
    cec
    #
    @0
    cA
    cL
    @3
    vx
    c.sm
    cS
    cL
    cN
    cY
    znzrh2.s
    znzrh2.r
    znzrh2.y
    znzrh2.2
    znzrh2
    fveq1d
    vx
    cA
    @2
    @4
    cz
    @3
    @1
    cA
    c.sm
    eceq1
    @3
    eqid
    c.sm
    cvv
    wcel
    @4
    cvv
    wcel
    c.sm
    zring
    cN
    csn
    cS
    cfv
    #
    cqg
    co
    cvv
    znzrh2.r
    zring
    @5
    cqg
    ovex
    eqeltri
    cA
    cvv
    c.sm
    ecexg
    ax-mp
    fvmpt
    sylan9eq
end
