include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "covoln.mm"
include "cfv.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cn.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wa.mm"
include "cxp.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wcel.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "0xr.mm"
include "pnfxr.mm"
include "cfn.mm"
include "adantr.mm"
include "elpwi.mm"
include "adantl.mm"
include "eqid.mm"
include "ovnsupge0.mm"
include "wne.mm"
include "ovnpnfelsup.mm"
include "ne0i.mm"
include "syl.mm"
include "inficc.mm"
include "ifcld.mm"
include "fmptd.mm"
include "ovnval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem ovnf
  let wph: wff ph
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume ovnf.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( voln* ` X ) : ~P ( RR ^m X ) --> ( 0 [,] +oo ) )

  proof
    wph
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    cX
    covoln
    cfv
    #
    wf
    @1
    @2
    vy
    @1
    cX
    c0
    wceq
    #
    cc0
    vy
    cv
    #
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
    vz
    cv
    vj
    cn
    cX
    @6
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
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cif
    #
    cmpt
    #
    wf
    wph
    vy
    @1
    @9
    @2
    @10
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @4
    cc0
    @8
    @2
    cc0
    @2
    wcel
    @12
    0e0iccpnf
    a1i
    @12
    cc0
    cpnf
    @7
    cc0
    cxr
    wcel
    @12
    0xr
    a1i
    cpnf
    cxr
    wcel
    @12
    pnfxr
    a1i
    @12
    vz
    @5
    vi
    vj
    vk
    @7
    cX
    wph
    cX
    cfn
    wcel
    @11
    ovnf.1
    adantr
    #
    @11
    @5
    @0
    wss
    wph
    @5
    @0
    elpwi
    adantl
    #
    @7
    eqid
    #
    ovnsupge0
    @12
    cpnf
    @7
    wcel
    @7
    c0
    wne
    @12
    vz
    @5
    vi
    vj
    vk
    @7
    cX
    @13
    @14
    @15
    ovnpnfelsup
    @7
    cpnf
    ne0i
    syl
    inficc
    ifcld
    @10
    eqid
    fmptd
    wph
    @1
    @2
    @3
    @10
    wph
    vy
    vz
    vi
    vj
    vk
    cX
    ovnf.1
    ovnval
    feq1d
    mpbird
end
