include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "ccoe.mm"
include "cn0.mm"
include "cmin.mm"
include "wceq.mm"
include "plyssc.mm"
include "simpl.mm"
include "sseldi.mm"
include "wss.mm"
include "ssid.mm"
include "neg1cn.mm"
include "plyconst.mm"
include "mp2an.mm"
include "simpr.mm"
include "plymulcl.mm"
include "sylancr.mm"
include "eqid.mm"
include "coeadd.mm"
include "syl2anc.mm"
include "coemulc.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "plyf.mm"
include "adantr.mm"
include "adantl.mm"
include "ofnegsub.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "nn0ex.mm"
include "coef3.mm"
include "3eqtr3d.mm"

theorem coesub
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vn: setvar n
  assume coesub.1: |- A = ( coeff ` F )
  assume coesub.2: |- B = ( coeff ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( coeff ` ( F oF - G ) ) = ( A oF - B ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cc
    c1
    cneg
    #
    csn
    #
    cxp
    #
    cG
    cmul
    cof
    #
    co
    #
    caddc
    cof
    #
    co
    #
    ccoe
    cfv
    #
    cA
    cn0
    @5
    cxp
    #
    cB
    @7
    co
    #
    @9
    co
    #
    cF
    cG
    cmin
    cof
    #
    co
    #
    ccoe
    cfv
    cA
    cB
    @15
    co
    #
    @3
    @11
    cA
    @8
    ccoe
    cfv
    #
    @9
    co
    #
    @14
    @3
    cF
    cc
    cply
    cfv
    #
    wcel
    @8
    @20
    wcel
    #
    @11
    @19
    wceq
    @3
    @0
    @20
    cF
    cS
    plyssc
    #
    @1
    @2
    simpl
    sseldi
    @3
    @6
    @20
    wcel
    #
    cG
    @20
    wcel
    #
    @21
    cc
    cc
    wss
    @4
    cc
    wcel
    #
    @23
    cc
    ssid
    neg1cn
    @4
    cc
    plyconst
    mp2an
    @3
    @0
    @20
    cG
    @22
    @1
    @2
    simpr
    sseldi
    #
    cc
    @6
    cG
    plymulcl
    sylancr
    cA
    @18
    cc
    cF
    @8
    coesub.1
    @18
    eqid
    coeadd
    syl2anc
    @3
    @18
    @13
    cA
    @9
    @3
    @18
    @12
    cG
    ccoe
    cfv
    #
    @7
    co
    #
    @13
    @3
    @25
    @24
    @18
    @28
    wceq
    neg1cn
    @26
    @4
    cc
    cG
    coemulc
    sylancr
    cB
    @27
    @12
    @7
    coesub.2
    oveq2i
    syl6eqr
    oveq2d
    eqtrd
    @3
    @10
    @16
    ccoe
    @3
    cc
    cvv
    wcel
    #
    cc
    cc
    cF
    wf
    #
    cc
    cc
    cG
    wf
    #
    @10
    @16
    wceq
    @29
    @3
    cnex
    a1i
    @1
    @30
    @2
    cS
    cF
    plyf
    adantr
    @2
    @31
    @1
    cS
    cG
    plyf
    adantl
    cc
    cF
    cG
    cvv
    ofnegsub
    syl3anc
    fveq2d
    @3
    cn0
    cvv
    wcel
    #
    cn0
    cc
    cA
    wf
    #
    cn0
    cc
    cB
    wf
    #
    @14
    @17
    wceq
    @32
    @3
    nn0ex
    a1i
    @1
    @33
    @2
    cA
    cS
    cF
    coesub.1
    coef3
    adantr
    @2
    @34
    @1
    cB
    cS
    cG
    coesub.2
    coef3
    adantl
    cn0
    cA
    cB
    cvv
    ofnegsub
    syl3anc
    3eqtr3d
end
