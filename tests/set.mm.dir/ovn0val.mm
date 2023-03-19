include "c0.mm"
include "covoln.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cn.mm"
include "cv.mm"
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
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "a1i.mm"
include "eqid.mm"
include "ovnval2.mm"
include "iftrue.mm"
include "ax-mp.mm"
include "eqtrd.mm"

theorem ovn0val
  let wph: wff ph
  let cA: class A
  let vi: setvar i
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume ovn0val.1: |- ( ph -> A C_ ( RR ^m (/) ) )


  assert |- ( ph -> ( ( voln* ` (/) ) ` A ) = 0 )

  proof
    wph
    cA
    c0
    covoln
    cfv
    cfv
    c0
    c0
    wceq
    #
    cc0
    cA
    vj
    cn
    vk
    c0
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
    c0
    @1
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
    c0
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
    cc0
    wph
    vz
    cA
    vi
    vj
    vk
    @2
    c0
    c0
    cfn
    wcel
    wph
    0fin
    a1i
    ovn0val.1
    @2
    eqid
    ovnval2
    @4
    cc0
    wceq
    #
    wph
    @0
    @5
    c0
    eqid
    @0
    cc0
    @3
    iftrue
    ax-mp
    a1i
    eqtrd
end
