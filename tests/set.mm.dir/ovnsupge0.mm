include "cn.mm"
include "cv.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "simp3.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "icossicc.mm"
include "nfv.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "wf.mm"
include "elmapi.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "ovnprodcl.mm"
include "sseldi.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0cl.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3adant3l.mm"
include "3exp.mm"
include "adantr.mm"
include "rexlimdv.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "syl5eqss.mm"

theorem ovnsupge0
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cX: class X
  let vx: setvar x
  assume ovnsupge0.1: |- ( ph -> X e. Fin )
  assume ovnsupge0.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnsupge0.3: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint X j
  disjoint X k
  disjoint j k
  disjoint i j
  disjoint i k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint i z
  disjoint ph z
  disjoint k x
  assert |- ( ph -> M C_ ( 0 [,] +oo ) )

  proof
    wph
    cM
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    cico
    vj
    cv
    #
    vi
    cv
    #
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    wss
    #
    vz
    cv
    #
    vj
    cn
    cX
    @2
    cvol
    cfv
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    cr
    cr
    cxp
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cc0
    cpnf
    cicc
    co
    #
    ovnsupge0.3
    wph
    @12
    @4
    @14
    wcel
    #
    wi
    #
    vz
    cxr
    wral
    @13
    @14
    wss
    wph
    @16
    vz
    cxr
    wph
    @4
    cxr
    wcel
    #
    wa
    @9
    @15
    vi
    @11
    wph
    @1
    @11
    wcel
    #
    @9
    @15
    wi
    wi
    @17
    wph
    @18
    @9
    @15
    wph
    @18
    @8
    @15
    @3
    wph
    @18
    @8
    w3a
    @4
    @7
    @14
    wph
    @18
    @8
    simp3
    wph
    @18
    @7
    @14
    wcel
    @8
    wph
    @18
    wa
    #
    @6
    cvv
    cn
    cn
    cvv
    wcel
    @19
    nnex
    a1i
    @19
    vj
    cn
    @5
    @14
    @6
    @19
    @0
    cn
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    @14
    @5
    cc0
    cpnf
    icossicc
    @21
    vk
    @1
    @0
    cX
    @21
    vk
    nfv
    wph
    cX
    cfn
    wcel
    @18
    @20
    ovnsupge0.1
    ad2antrr
    @18
    cn
    @10
    @1
    wf
    wph
    @20
    @1
    @10
    cn
    elmapi
    ad2antlr
    @19
    @20
    simpr
    ovnprodcl
    sseldi
    @6
    eqid
    fmptd
    sge0cl
    3adant3
    eqeltrd
    3adant3l
    3exp
    adantr
    rexlimdv
    ralrimiva
    @12
    vz
    cxr
    @14
    rabss
    sylibr
    syl5eqss
end
