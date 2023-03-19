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
include "recni.mm"
include "mulcli.mm"
include "normlem0.mm"
include "cjmuli.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cjrebi.mm"
include "mpbi.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "negeqi.mm"
include "cjcli.mm"
include "mulneg2i.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "eqcomi.mm"
include "mul4i.mm"
include "c1.mm"
include "cabs.mm"
include "absvalsqi.mm"
include "sq1.mm"
include "3eqtr3i.mm"
include "oveq12i.mm"
include "mulid2i.mm"
include "sqvali.mm"

theorem normlem1
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H
  assume normlem1.4: |- R e. RR
  assume normlem1.5: |- ( abs ` S ) = 1


  assert |- ( ( F -h ( ( S x. R ) .h G ) ) .ih ( F -h ( ( S x. R ) .h G ) ) ) = ( ( ( F .ih F ) + ( ( ( * ` S ) x. -u R ) x. ( F .ih G ) ) ) + ( ( ( S x. -u R ) x. ( G .ih F ) ) + ( ( R ^ 2 ) x. ( G .ih G ) ) ) )

  proof
    cF
    cS
    cR
    cmul
    co
    #
    cG
    csm
    co
    cmv
    co
    #
    @1
    csp
    co
    cF
    cF
    csp
    co
    #
    @0
    ccj
    cfv
    #
    cneg
    #
    cF
    cG
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @0
    cneg
    #
    cG
    cF
    csp
    co
    #
    cmul
    co
    #
    @0
    @3
    cmul
    co
    #
    cG
    cG
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @2
    cS
    ccj
    cfv
    #
    cR
    cneg
    #
    cmul
    co
    #
    @5
    cmul
    co
    #
    caddc
    co
    #
    cS
    @16
    cmul
    co
    #
    @9
    cmul
    co
    #
    cR
    c2
    cexp
    co
    #
    @12
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @0
    cF
    cG
    cS
    cR
    normlem1.1
    cR
    normlem1.4
    recni
    #
    mulcli
    normlem1.2
    normlem1.3
    normlem0
    @7
    @19
    @14
    @24
    caddc
    @6
    @18
    @2
    caddc
    @4
    @17
    @5
    cmul
    @4
    @15
    cR
    cmul
    co
    #
    cneg
    @17
    @3
    @26
    @3
    @15
    cR
    ccj
    cfv
    #
    cmul
    co
    #
    @26
    cS
    cR
    normlem1.1
    @25
    cjmuli
    #
    @27
    cR
    @15
    cmul
    cR
    cr
    wcel
    @27
    cR
    wceq
    normlem1.4
    cR
    @25
    cjrebi
    mpbi
    #
    oveq2i
    eqtri
    negeqi
    @15
    cR
    cS
    normlem1.1
    cjcli
    #
    @25
    mulneg2i
    eqtr4i
    oveq1i
    oveq2i
    @10
    @21
    @13
    @23
    caddc
    @8
    @20
    @9
    cmul
    @20
    @8
    cS
    cR
    normlem1.1
    @25
    mulneg2i
    eqcomi
    oveq1i
    @11
    @22
    @12
    cmul
    @11
    cR
    cR
    cmul
    co
    #
    @22
    @11
    @0
    @28
    cmul
    co
    #
    @32
    @3
    @28
    @0
    cmul
    @29
    oveq2i
    @33
    cS
    @15
    cmul
    co
    #
    cR
    @27
    cmul
    co
    #
    cmul
    co
    #
    @32
    cS
    cR
    @15
    @27
    normlem1.1
    @25
    @31
    cR
    @25
    cjcli
    mul4i
    @36
    c1
    @32
    cmul
    co
    @32
    @34
    c1
    @35
    @32
    cmul
    cS
    cabs
    cfv
    #
    c2
    cexp
    co
    c1
    c2
    cexp
    co
    @34
    c1
    @37
    c1
    c2
    cexp
    normlem1.5
    oveq1i
    cS
    normlem1.1
    absvalsqi
    sq1
    3eqtr3i
    @27
    cR
    cR
    cmul
    @30
    oveq2i
    oveq12i
    @32
    cR
    cR
    @25
    @25
    mulcli
    mulid2i
    eqtri
    eqtri
    eqtri
    cR
    @25
    sqvali
    eqtr4i
    oveq1i
    oveq12i
    oveq12i
    eqtri
end
