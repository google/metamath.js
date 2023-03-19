include "cv.mm"
include "covoln.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "nfv.mm"
include "wss.mm"
include "cn.mm"
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
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "cpnf.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ovnpnfelsup.mm"
include "ne0i.mm"
include "syl.mm"
include "cc0.mm"
include "wral.mm"
include "0red.mm"
include "cicc.mm"
include "ovnsupge0.mm"
include "0xr.mm"
include "pnfxr.mm"
include "ssel2.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "infrpge.mm"
include "w3a.mm"
include "simp3.mm"
include "ovnn0val.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "breqtrd.mm"
include "3exp.mm"
include "reximdai.mm"
include "mpd.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "cbvrexf.mm"
include "sylib.mm"

theorem ovnlerp
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cM: class M
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume ovnlerp.x: |- ( ph -> X e. Fin )
  assume ovnlerp.n0: |- ( ph -> X =/= (/) )
  assume ovnlerp.a: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnlerp.e: |- ( ph -> E e. RR+ )
  assume ovnlerp.m: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint A i
  disjoint A z
  disjoint i z
  disjoint E z
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
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint A w
  disjoint w z
  disjoint E w
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint x y
  disjoint X w
  disjoint ph w
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. z e. M z <_ ( ( ( voln* ` X ) ` A ) +e E ) )

  proof
    wph
    vw
    cv
    #
    cA
    cX
    covoln
    cfv
    cfv
    #
    cE
    cxad
    co
    #
    cle
    wbr
    #
    vw
    cM
    wrex
    #
    vz
    cv
    #
    @2
    cle
    wbr
    #
    vz
    cM
    wrex
    wph
    @0
    cM
    cxr
    clt
    cinf
    #
    cE
    cxad
    co
    #
    cle
    wbr
    #
    vw
    cM
    wrex
    @4
    wph
    vx
    vy
    vw
    cM
    cE
    wph
    vx
    nfv
    cM
    cxr
    wss
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
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    wss
    @5
    vj
    cn
    cX
    @10
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    wa
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
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    ovnlerp.m
    @11
    vz
    cxr
    ssrab2
    eqsstri
    a1i
    wph
    cpnf
    cM
    wcel
    cM
    c0
    wne
    wph
    vz
    cA
    vi
    vj
    vk
    cM
    cX
    ovnlerp.x
    ovnlerp.a
    ovnlerp.m
    ovnpnfelsup
    cM
    cpnf
    ne0i
    syl
    wph
    cc0
    cr
    wcel
    cc0
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cM
    wral
    #
    vx
    cv
    #
    @13
    cle
    wbr
    #
    vy
    cM
    wral
    #
    vx
    cr
    wrex
    wph
    0red
    wph
    cM
    cc0
    cpnf
    cicc
    co
    #
    wss
    #
    @15
    wph
    vz
    cA
    vi
    vj
    vk
    cM
    cX
    ovnlerp.x
    ovnlerp.a
    ovnlerp.m
    ovnsupge0
    @20
    @14
    vy
    cM
    @20
    @13
    cM
    wcel
    wa
    #
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @13
    @19
    wcel
    @14
    @22
    @21
    0xr
    a1i
    @23
    @21
    pnfxr
    a1i
    cM
    @19
    @13
    ssel2
    cc0
    cpnf
    @13
    iccgelb
    syl3anc
    ralrimiva
    syl
    @18
    @15
    vx
    cc0
    cr
    @16
    cc0
    wceq
    @17
    @14
    vy
    cM
    @16
    cc0
    @13
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    ovnlerp.e
    infrpge
    wph
    @9
    @3
    vw
    cM
    wph
    vw
    nfv
    wph
    @0
    cM
    wcel
    #
    @9
    @3
    wph
    @24
    @9
    w3a
    @0
    @8
    @2
    cle
    wph
    @24
    @9
    simp3
    wph
    @24
    @8
    @2
    wceq
    @9
    wph
    @7
    @1
    cE
    cxad
    wph
    @1
    @7
    wph
    vz
    cA
    vi
    vj
    vk
    cM
    cX
    ovnlerp.x
    ovnlerp.n0
    ovnlerp.a
    ovnlerp.m
    ovnn0val
    eqcomd
    oveq1d
    3ad2ant1
    breqtrd
    3exp
    reximdai
    mpd
    @3
    @6
    vw
    vz
    cM
    vw
    cM
    nfcv
    vz
    cM
    @12
    ovnlerp.m
    @11
    vz
    cxr
    nfrab1
    nfcxfr
    @3
    vz
    nfv
    @6
    vw
    nfv
    @0
    @5
    @2
    cle
    breq1
    cbvrexf
    sylib
end
