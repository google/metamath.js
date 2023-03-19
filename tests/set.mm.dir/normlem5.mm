include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "cmv.mm"
include "csp.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cle.mm"
include "chil.mm"
include "wcel.mm"
include "wbr.mm"
include "recni.mm"
include "mulcli.mm"
include "hvmulcli.mm"
include "hvsubcli.mm"
include "hiidge0.mm"
include "ax-mp.mm"
include "normlem4.mm"
include "breqtri.mm"

theorem normlem5
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


  assert |- 0 <_ ( ( ( A x. ( R ^ 2 ) ) + ( B x. R ) ) + C )

  proof
    cc0
    cF
    cS
    cR
    cmul
    co
    #
    cG
    csm
    co
    #
    cmv
    co
    #
    @2
    csp
    co
    #
    cA
    cR
    c2
    cexp
    co
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
    cle
    @2
    chil
    wcel
    cc0
    @3
    cle
    wbr
    cF
    @1
    normlem1.2
    @0
    cG
    cS
    cR
    normlem1.1
    cR
    normlem4.7
    recni
    mulcli
    normlem1.3
    hvmulcli
    hvsubcli
    @2
    hiidge0
    ax-mp
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
    normlem4.8
    normlem4
    breqtri
end
