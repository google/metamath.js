include "csm.mm"
include "co.mm"
include "cmv.mm"
include "csp.mm"
include "cneg.mm"
include "cva.mm"
include "caddc.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "c1.mm"
include "hvmulcli.mm"
include "hvsubvali.mm"
include "mulm1i.mm"
include "oveq1i.mm"
include "neg1cn.mm"
include "hvmulassi.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "oveq12i.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "negcli.mm"
include "hvaddcli.mm"
include "ax-his2.mm"
include "mp3an.mm"
include "his7.mm"
include "cc.mm"
include "his5.mm"
include "cjnegi.mm"
include "eqtri.mm"
include "ax-his3.mm"
include "hicli.mm"
include "cjcli.mm"
include "mulcli.mm"
include "adddii.mm"
include "mulassi.mm"
include "mul2negi.mm"
include "3eqtri.mm"

theorem normlem0
  let cS: class S
  let cF: class F
  let cG: class G
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H


  assert |- ( ( F -h ( S .h G ) ) .ih ( F -h ( S .h G ) ) ) = ( ( ( F .ih F ) + ( -u ( * ` S ) x. ( F .ih G ) ) ) + ( ( -u S x. ( G .ih F ) ) + ( ( S x. ( * ` S ) ) x. ( G .ih G ) ) ) )

  proof
    cF
    cS
    cG
    csm
    co
    #
    cmv
    co
    #
    @1
    csp
    co
    cF
    cS
    cneg
    #
    cG
    csm
    co
    #
    cva
    co
    #
    @4
    csp
    co
    #
    cF
    @4
    csp
    co
    #
    @3
    @4
    csp
    co
    #
    caddc
    co
    #
    cF
    cF
    csp
    co
    #
    cS
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
    @2
    cG
    cF
    csp
    co
    #
    cmul
    co
    #
    cS
    @10
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
    @1
    @4
    @1
    @4
    csp
    @1
    cF
    c1
    cneg
    #
    @0
    csm
    co
    #
    cva
    co
    @4
    cF
    @0
    normlem1.2
    cS
    cG
    normlem1.1
    normlem1.3
    hvmulcli
    hvsubvali
    @3
    @22
    cF
    cva
    @21
    cS
    cmul
    co
    #
    cG
    csm
    co
    @3
    @22
    @23
    @2
    cG
    csm
    cS
    normlem1.1
    mulm1i
    oveq1i
    @21
    cS
    cG
    neg1cn
    normlem1.1
    normlem1.3
    hvmulassi
    eqtr3i
    oveq2i
    eqtr4i
    #
    @24
    oveq12i
    cF
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @5
    @8
    wceq
    normlem1.2
    @2
    cG
    cS
    normlem1.1
    negcli
    #
    normlem1.3
    hvmulcli
    #
    cF
    @3
    normlem1.2
    @29
    hvaddcli
    #
    cF
    @3
    @4
    ax-his2
    mp3an
    @6
    @14
    @7
    @20
    caddc
    @6
    @9
    cF
    @3
    csp
    co
    #
    caddc
    co
    #
    @14
    @25
    @25
    @26
    @6
    @32
    wceq
    normlem1.2
    normlem1.2
    @29
    cF
    cF
    @3
    his7
    mp3an
    @31
    @13
    @9
    caddc
    @31
    @2
    ccj
    cfv
    #
    @12
    cmul
    co
    #
    @13
    @2
    cc
    wcel
    #
    @25
    cG
    chil
    wcel
    #
    @31
    @34
    wceq
    @28
    normlem1.2
    normlem1.3
    @2
    cF
    cG
    his5
    mp3an
    @33
    @11
    @12
    cmul
    cS
    normlem1.1
    cjnegi
    #
    oveq1i
    eqtri
    oveq2i
    eqtri
    @7
    @2
    cG
    @4
    csp
    co
    #
    cmul
    co
    #
    @2
    @15
    @33
    @18
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @20
    @35
    @36
    @27
    @7
    @39
    wceq
    @28
    normlem1.3
    @30
    @2
    cG
    @4
    ax-his3
    mp3an
    @38
    @41
    @2
    cmul
    @38
    @15
    cG
    @3
    csp
    co
    #
    caddc
    co
    #
    @41
    @36
    @25
    @26
    @38
    @44
    wceq
    normlem1.3
    normlem1.2
    @29
    cG
    cF
    @3
    his7
    mp3an
    @43
    @40
    @15
    caddc
    @35
    @36
    @36
    @43
    @40
    wceq
    @28
    normlem1.3
    normlem1.3
    @2
    cG
    cG
    his5
    mp3an
    oveq2i
    eqtri
    oveq2i
    @42
    @16
    @2
    @40
    cmul
    co
    #
    caddc
    co
    @20
    @2
    @15
    @40
    @28
    cG
    cF
    normlem1.3
    normlem1.2
    hicli
    @33
    @18
    @2
    @28
    cjcli
    #
    cG
    cG
    normlem1.3
    normlem1.3
    hicli
    #
    mulcli
    adddii
    @45
    @19
    @16
    caddc
    @2
    @33
    cmul
    co
    #
    @18
    cmul
    co
    @45
    @19
    @2
    @33
    @18
    @28
    @46
    @47
    mulassi
    @48
    @17
    @18
    cmul
    @48
    @2
    @11
    cmul
    co
    @17
    @33
    @11
    @2
    cmul
    @37
    oveq2i
    cS
    @10
    normlem1.1
    cS
    normlem1.1
    cjcli
    mul2negi
    eqtri
    oveq1i
    eqtr3i
    oveq2i
    eqtri
    3eqtri
    oveq12i
    3eqtri
end
