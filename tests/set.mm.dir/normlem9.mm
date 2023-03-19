include "cmv.mm"
include "co.mm"
include "csp.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "caddc.mm"
include "cmin.mm"
include "hvsubvali.mm"
include "oveq12i.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "normlem8.mm"
include "cmul.mm"
include "ccj.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wceq.mm"
include "ax-his3.mm"
include "mp3an.mm"
include "his5.mm"
include "oveq2i.mm"
include "cr.mm"
include "neg1rr.mm"
include "cjre.mm"
include "ax-mp.mm"
include "ax-1cn.mm"
include "mul2negi.mm"
include "mulid2i.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "cjcli.mm"
include "hicli.mm"
include "mulassi.mm"
include "3eqtr3i.mm"
include "mulm1i.mm"
include "eqtri.mm"
include "negdii.mm"
include "eqtr4i.mm"
include "addcli.mm"
include "negsubi.mm"

theorem normlem9
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume normlem8.1: |- A e. ~H
  assume normlem8.2: |- B e. ~H
  assume normlem8.3: |- C e. ~H
  assume normlem8.4: |- D e. ~H


  assert |- ( ( A -h B ) .ih ( C -h D ) ) = ( ( ( A .ih C ) + ( B .ih D ) ) - ( ( A .ih D ) + ( B .ih C ) ) )

  proof
    cA
    cB
    cmv
    co
    #
    cC
    cD
    cmv
    co
    #
    csp
    co
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    cC
    @2
    cD
    csm
    co
    #
    cva
    co
    #
    csp
    co
    cA
    cC
    csp
    co
    #
    @3
    @5
    csp
    co
    #
    caddc
    co
    #
    cA
    @5
    csp
    co
    #
    @3
    cC
    csp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @7
    cB
    cD
    csp
    co
    #
    caddc
    co
    #
    cA
    cD
    csp
    co
    #
    cB
    cC
    csp
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @0
    @4
    @1
    @6
    csp
    cA
    cB
    normlem8.1
    normlem8.2
    hvsubvali
    cC
    cD
    normlem8.3
    normlem8.4
    hvsubvali
    oveq12i
    cA
    @3
    cC
    @5
    normlem8.1
    @2
    cB
    neg1cn
    normlem8.2
    hvmulcli
    normlem8.3
    @2
    cD
    neg1cn
    normlem8.4
    hvmulcli
    #
    normlem8
    @13
    @15
    @18
    cneg
    #
    caddc
    co
    @19
    @9
    @15
    @12
    @21
    caddc
    @8
    @14
    @7
    caddc
    @8
    @2
    cB
    @5
    csp
    co
    #
    cmul
    co
    #
    @2
    @2
    ccj
    cfv
    #
    @14
    cmul
    co
    #
    cmul
    co
    #
    @14
    @2
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    @5
    chil
    wcel
    @8
    @23
    wceq
    neg1cn
    normlem8.2
    @20
    @2
    cB
    @5
    ax-his3
    mp3an
    @22
    @25
    @2
    cmul
    @27
    @28
    cD
    chil
    wcel
    #
    @22
    @25
    wceq
    neg1cn
    normlem8.2
    normlem8.4
    @2
    cB
    cD
    his5
    mp3an
    oveq2i
    @2
    @24
    cmul
    co
    #
    @14
    cmul
    co
    c1
    @14
    cmul
    co
    @26
    @14
    @30
    c1
    @14
    cmul
    @30
    @2
    @2
    cmul
    co
    c1
    c1
    cmul
    co
    c1
    @24
    @2
    @2
    cmul
    @2
    cr
    wcel
    @24
    @2
    wceq
    neg1rr
    @2
    cjre
    ax-mp
    #
    oveq2i
    c1
    c1
    ax-1cn
    ax-1cn
    mul2negi
    c1
    ax-1cn
    mulid2i
    3eqtri
    oveq1i
    @2
    @24
    @14
    neg1cn
    @2
    neg1cn
    cjcli
    cB
    cD
    normlem8.2
    normlem8.4
    hicli
    #
    mulassi
    @14
    @32
    mulid2i
    3eqtr3i
    3eqtri
    oveq2i
    @12
    @16
    cneg
    #
    @17
    cneg
    #
    caddc
    co
    @21
    @10
    @33
    @11
    @34
    caddc
    @10
    @24
    @16
    cmul
    co
    #
    @2
    @16
    cmul
    co
    @33
    @27
    cA
    chil
    wcel
    @29
    @10
    @35
    wceq
    neg1cn
    normlem8.1
    normlem8.4
    @2
    cA
    cD
    his5
    mp3an
    @24
    @2
    @16
    cmul
    @31
    oveq1i
    @16
    cA
    cD
    normlem8.1
    normlem8.4
    hicli
    #
    mulm1i
    3eqtri
    @11
    @2
    @17
    cmul
    co
    #
    @34
    @27
    @28
    cC
    chil
    wcel
    @11
    @37
    wceq
    neg1cn
    normlem8.2
    normlem8.3
    @2
    cB
    cC
    ax-his3
    mp3an
    @17
    cB
    cC
    normlem8.2
    normlem8.3
    hicli
    #
    mulm1i
    eqtri
    oveq12i
    @16
    @17
    @36
    @38
    negdii
    eqtr4i
    oveq12i
    @15
    @18
    @7
    @14
    cA
    cC
    normlem8.1
    normlem8.3
    hicli
    @32
    addcli
    @16
    @17
    @36
    @38
    addcli
    negsubi
    eqtri
    3eqtri
end
