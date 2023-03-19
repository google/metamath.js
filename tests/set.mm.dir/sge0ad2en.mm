include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cn.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cr.mm"
include "cico.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "adantr.mm"
include "2re.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantl.mm"
include "reexpcld.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "redivcld.mm"
include "rexrd.mm"
include "crp.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "cle.mm"
include "wbr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "divge0d.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "1zzd.mm"
include "nnuz.mm"
include "cc.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "recnd.mm"
include "eqid.mm"
include "geo2lim.mm"
include "syl.mm"
include "sge0isummpt.mm"

theorem sge0ad2en
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume sge0ad2en.1: |- ( ph -> A e. ( 0 [,) +oo ) )

  disjoint A n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( n e. NN |-> ( A / ( 2 ^ n ) ) ) ) = A )

  proof
    wph
    cA
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cA
    vn
    c1
    cn
    wph
    vn
    nfv
    wph
    @0
    cn
    wcel
    #
    wa
    #
    cc0
    cpnf
    @2
    cc0
    cxr
    wcel
    #
    @4
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    @4
    pnfxr
    a1i
    @4
    @2
    @4
    cA
    @1
    wph
    cA
    cr
    wcel
    @3
    wph
    cc0
    cpnf
    cico
    co
    #
    cr
    cA
    rge0ssre
    sge0ad2en.1
    sseldi
    #
    adantr
    #
    @4
    c2
    @0
    c2
    cr
    wcel
    @4
    2re
    a1i
    @3
    @0
    cn0
    wcel
    wph
    @0
    nnnn0
    adantl
    #
    reexpcld
    @4
    c2
    @0
    @4
    2cnd
    c2
    cc0
    wne
    @4
    2ne0
    a1i
    @4
    @0
    @10
    nn0zd
    #
    expne0d
    redivcld
    #
    rexrd
    @4
    cA
    @1
    @9
    @4
    c2
    @0
    c2
    crp
    wcel
    @4
    2rp
    a1i
    @11
    rpexpcld
    wph
    cc0
    cA
    cle
    wbr
    #
    @3
    wph
    @5
    @6
    cA
    @7
    wcel
    @13
    @5
    wph
    0xr
    a1i
    @6
    wph
    pnfxr
    a1i
    sge0ad2en.1
    cc0
    cpnf
    cA
    icogelb
    syl3anc
    adantr
    divge0d
    @4
    @2
    @12
    ltpnfd
    elicod
    wph
    1zzd
    nnuz
    wph
    cA
    cc
    wcel
    caddc
    vn
    cn
    @2
    cmpt
    #
    c1
    cseq
    cA
    cli
    wbr
    wph
    cA
    @8
    recnd
    cA
    vn
    @14
    @14
    eqid
    geo2lim
    syl
    sge0isummpt
end
