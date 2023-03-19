include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "csp.mm"
include "ccj.mm"
include "cfv.mm"
include "cneg.mm"
include "cc.mm"
include "hicli.mm"
include "eqeltri.mm"
include "recni.mm"
include "sqcli.mm"
include "mulcli.mm"
include "normlem2.mm"
include "addcomi.mm"
include "cjcli.mm"
include "addcli.mm"
include "mulneg1i.mm"
include "oveq1i.mm"
include "mulneg2i.mm"
include "3eqtr4i.mm"
include "negcli.mm"
include "adddiri.mm"
include "mul32i.mm"
include "oveq12i.mm"
include "3eqtri.mm"
include "oveq2i.mm"
include "mulcomli.mm"
include "addassi.mm"

theorem normlem3
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
  assume normlem3.7: |- R e. RR


  assert |- ( ( ( A x. ( R ^ 2 ) ) + ( B x. R ) ) + C ) = ( ( ( F .ih F ) + ( ( ( * ` S ) x. -u R ) x. ( F .ih G ) ) ) + ( ( ( S x. -u R ) x. ( G .ih F ) ) + ( ( R ^ 2 ) x. ( G .ih G ) ) ) )

  proof
    cC
    cA
    cR
    c2
    cexp
    co
    #
    cmul
    co
    #
    cB
    cR
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    cF
    cF
    csp
    co
    #
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
    cF
    cG
    csp
    co
    #
    cmul
    co
    #
    cS
    @6
    cmul
    co
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
    #
    caddc
    co
    @3
    cC
    caddc
    co
    @4
    @9
    caddc
    co
    @15
    caddc
    co
    cC
    @4
    @3
    @16
    caddc
    normlem3.6
    @3
    @2
    @1
    caddc
    co
    @9
    @12
    caddc
    co
    #
    @14
    caddc
    co
    @16
    @1
    @2
    cA
    @0
    cA
    @13
    cc
    normlem3.5
    cG
    cG
    normlem1.3
    normlem1.3
    hicli
    #
    eqeltri
    #
    cR
    cR
    normlem3.7
    recni
    #
    sqcli
    #
    mulcli
    #
    cB
    cR
    cB
    cB
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    normlem2.4
    normlem2
    recni
    @20
    mulcli
    #
    addcomi
    @2
    @17
    @1
    @14
    caddc
    @2
    @5
    @8
    cmul
    co
    #
    cS
    @11
    cmul
    co
    #
    caddc
    co
    #
    @6
    cmul
    co
    #
    @24
    @6
    cmul
    co
    #
    @25
    @6
    cmul
    co
    #
    caddc
    co
    @17
    @26
    cneg
    #
    cR
    cmul
    co
    @26
    cR
    cmul
    co
    cneg
    @2
    @27
    @26
    cR
    @24
    @25
    @5
    @8
    cS
    normlem1.1
    cjcli
    #
    cF
    cG
    normlem1.2
    normlem1.3
    hicli
    #
    mulcli
    #
    cS
    @11
    normlem1.1
    cG
    cF
    normlem1.3
    normlem1.2
    hicli
    #
    mulcli
    #
    addcli
    #
    @20
    mulneg1i
    cB
    @30
    cR
    cmul
    normlem2.4
    oveq1i
    @26
    cR
    @36
    @20
    mulneg2i
    3eqtr4i
    @24
    @25
    @6
    @33
    @35
    cR
    @20
    negcli
    #
    adddiri
    @28
    @9
    @29
    @12
    caddc
    @5
    @8
    @6
    @31
    @32
    @37
    mul32i
    cS
    @11
    @6
    normlem1.1
    @34
    @37
    mul32i
    oveq12i
    3eqtri
    @0
    cA
    @14
    @21
    @19
    cA
    @13
    @0
    cmul
    normlem3.5
    oveq2i
    mulcomli
    oveq12i
    @9
    @12
    @14
    @7
    @8
    @5
    @6
    @31
    @37
    mulcli
    @32
    mulcli
    #
    @10
    @11
    cS
    @6
    normlem1.1
    @37
    mulcli
    @34
    mulcli
    #
    @0
    @13
    @21
    @18
    mulcli
    #
    addassi
    3eqtri
    oveq12i
    @3
    cC
    @1
    @2
    @22
    @23
    addcli
    cC
    @4
    cc
    normlem3.6
    cF
    cF
    normlem1.2
    normlem1.2
    hicli
    #
    eqeltri
    addcomi
    @4
    @9
    @15
    @41
    @38
    @12
    @14
    @39
    @40
    addcli
    addassi
    3eqtr4i
end
