include "covoln.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
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
include "crab.mm"
include "wi.mm"
include "wral.mm"
include "adantr.mm"
include "simpr.mm"
include "sstrd.mm"
include "adantrr.mm"
include "id.mm"
include "ad2antll.mm"
include "jca.mm"
include "ex.mm"
include "reximdv.mm"
include "ralrimivw.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "a1i.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "infxrss.mm"
include "syl2anc.mm"
include "ovnn0val.mm"
include "breq12d.mm"

theorem ovnsslelem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  assume ovnsslelem.1: |- ( ph -> X e. Fin )
  assume ovnsslelem.2: |- ( ph -> X =/= (/) )
  assume ovnsslelem.3: |- ( ph -> A C_ B )
  assume ovnsslelem.4: |- ( ph -> B C_ ( RR ^m X ) )
  assume ovnsslelem.5: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }
  assume ovnsslelem.6: |- N = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( B C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint A i
  disjoint A z
  disjoint i z
  disjoint B i
  disjoint B z
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint i ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` A ) <_ ( ( voln* ` X ) ` B ) )

  proof
    wph
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    cB
    @0
    cfv
    #
    cle
    wbr
    cM
    cxr
    clt
    cinf
    #
    cN
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    wph
    cN
    cM
    wss
    #
    cM
    cxr
    wss
    #
    @5
    wph
    @6
    cB
    vj
    cn
    vk
    cX
    vk
    cv
    cico
    vj
    cv
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    #
    wss
    #
    vz
    cv
    vj
    cn
    cX
    @8
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
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
    cA
    @9
    wss
    #
    @11
    wa
    #
    vi
    @13
    wrex
    #
    vz
    cxr
    crab
    #
    wss
    #
    wph
    @14
    @18
    wi
    #
    vz
    cxr
    wral
    @20
    wph
    @21
    vz
    cxr
    wph
    @12
    @17
    vi
    @13
    wph
    @12
    @17
    wph
    @12
    wa
    @16
    @11
    wph
    @10
    @16
    @11
    wph
    @10
    wa
    cA
    cB
    @9
    wph
    cA
    cB
    wss
    @10
    ovnsslelem.3
    adantr
    wph
    @10
    simpr
    sstrd
    adantrr
    @11
    @11
    wph
    @10
    @11
    id
    ad2antll
    jca
    ex
    reximdv
    ralrimivw
    @14
    @18
    vz
    cxr
    ss2rab
    sylibr
    wph
    cN
    @15
    cM
    @19
    cN
    @15
    wceq
    wph
    ovnsslelem.6
    a1i
    cM
    @19
    wceq
    wph
    ovnsslelem.5
    a1i
    sseq12d
    mpbird
    @7
    wph
    cM
    @19
    cxr
    ovnsslelem.5
    @18
    vz
    cxr
    ssrab2
    eqsstri
    a1i
    cN
    cM
    infxrss
    syl2anc
    wph
    @1
    @3
    @2
    @4
    cle
    wph
    vz
    cA
    vi
    vj
    vk
    cM
    cX
    ovnsslelem.1
    ovnsslelem.2
    wph
    cA
    cB
    cr
    cX
    cmap
    co
    ovnsslelem.3
    ovnsslelem.4
    sstrd
    ovnsslelem.5
    ovnn0val
    wph
    vz
    cB
    vi
    vj
    vk
    cN
    cX
    ovnsslelem.1
    ovnsslelem.2
    ovnsslelem.4
    ovnsslelem.6
    ovnn0val
    breq12d
    mpbird
end
