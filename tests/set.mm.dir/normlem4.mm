include "cmul.mm"
include "co.mm"
include "csm.mm"
include "cmv.mm"
include "csp.mm"
include "ccj.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "normlem1.mm"
include "normlem3.mm"
include "eqtr4i.mm"

theorem normlem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H
  assume normlem2.4: |- B = -u ( ( ( * ` S ) x. ( F .ih G ) ) + ( S x. ( G .ih F ) ) )
  assume normlem3.5: |- A = ( G .ih G )
  assume normlem3.6: |- C = ( F .ih F )
  assume normlem4.7: |- R e. RR
  assume normlem4.8: |- ( abs ` S ) = 1


  assert |- ( ( F -h ( ( S x. R ) .h G ) ) .ih ( F -h ( ( S x. R ) .h G ) ) ) = ( ( ( A x. ( R ^ 2 ) ) + ( B x. R ) ) + C )

  proof
    cF
    cS
    cR
    cmul
    co
    cG
    csm
    co
    cmv
    co
    #
    @0
    csp
    co
    cF
    cF
    csp
    co
    cS
    ccj
    cfv
    cR
    cneg
    #
    cmul
    co
    cF
    cG
    csp
    co
    cmul
    co
    caddc
    co
    cS
    @1
    cmul
    co
    cG
    cF
    csp
    co
    cmul
    co
    cR
    c2
    cexp
    co
    #
    cG
    cG
    csp
    co
    cmul
    co
    caddc
    co
    caddc
    co
    cA
    @2
    cmul
    co
    cB
    cR
    cmul
    co
    caddc
    co
    cC
    caddc
    co
    cR
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    normlem4.7
    normlem4.8
    normlem1
    cA
    cB
    cC
    cR
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    normlem2.4
    normlem3.5
    normlem3.6
    normlem4.7
    normlem3
    eqtr4i
end
