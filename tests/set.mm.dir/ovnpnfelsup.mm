include "cpnf.mm"
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
include "wcel.mm"
include "pnfxr.mm"
include "a1i.mm"
include "hoicvrrex.mm"
include "jca.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "eqcomi.mm"
include "eleqtrd.mm"

theorem ovnpnfelsup
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cX: class X
  let vx: setvar x
  assume ovnpnfelsup.1: |- ( ph -> X e. Fin )
  assume ovnpnfelsup.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnpnfelsup.3: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint A i
  disjoint A z
  disjoint i z
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> +oo e. M )

  proof
    wph
    cpnf
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
    #
    vz
    cv
    #
    vj
    cn
    cX
    @0
    cvol
    cfv
    vk
    cprod
    cmpt
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
    cM
    wph
    cpnf
    cxr
    wcel
    #
    @1
    cpnf
    @3
    wceq
    #
    wa
    #
    vi
    @6
    wrex
    #
    wa
    cpnf
    @8
    wcel
    wph
    @9
    @12
    @9
    wph
    pnfxr
    a1i
    wph
    vi
    vj
    vk
    cX
    cA
    ovnpnfelsup.1
    ovnpnfelsup.2
    hoicvrrex
    jca
    @7
    @12
    vz
    cpnf
    cxr
    @2
    cpnf
    wceq
    #
    @5
    @11
    vi
    @6
    @13
    @4
    @10
    @1
    @2
    cpnf
    @3
    eqeq1
    anbi2d
    rexbidv
    elrab
    sylibr
    @8
    cM
    wceq
    wph
    cM
    @8
    ovnpnfelsup.3
    eqcomi
    a1i
    eleqtrd
end
