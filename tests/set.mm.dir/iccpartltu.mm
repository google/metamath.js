include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "c1.mm"
include "cun.mm"
include "caddc.mm"
include "cz.mm"
include "w3a.mm"
include "wceq.mm"
include "cn.mm"
include "0zd.mm"
include "nnz.mm"
include "nngt0.mm"
include "3jca.mm"
include "syl.mm"
include "fzopred.mm"
include "0p1e1.mm"
include "a1i.mm"
include "oveq1d.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "wo.mm"
include "elun.mm"
include "wi.mm"
include "elsni.mm"
include "wa.mm"
include "fveq2.mm"
include "adantr.mm"
include "iccpartlt.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "wral.mm"
include "weq.mm"
include "breq1d.mm"
include "rspccv.mm"
include "iccpartiltu.mm"
include "syl11.mm"
include "jaoi.mm"
include "com12.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem iccpartltu
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M k
  disjoint i k
  disjoint P k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> A. i e. ( 0 ..^ M ) ( P ` i ) < ( P ` M ) )

  proof
    wph
    vi
    cv
    #
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wph
    @0
    @4
    wcel
    @0
    cc0
    csn
    #
    c1
    cM
    cfzo
    co
    #
    cun
    #
    wcel
    #
    @3
    wph
    @4
    @7
    @0
    wph
    @4
    @5
    cc0
    c1
    caddc
    co
    #
    cM
    cfzo
    co
    #
    cun
    #
    @7
    wph
    cc0
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cc0
    cM
    clt
    wbr
    #
    w3a
    #
    @4
    @11
    wceq
    wph
    cM
    cn
    wcel
    #
    @15
    iccpartgtprec.m
    @16
    @12
    @13
    @14
    @16
    0zd
    cM
    nnz
    cM
    nngt0
    3jca
    syl
    cc0
    cM
    fzopred
    syl
    wph
    @10
    @6
    @5
    wph
    @9
    c1
    cM
    cfzo
    @9
    c1
    wceq
    wph
    0p1e1
    a1i
    oveq1d
    uneq2d
    eqtrd
    eleq2d
    @8
    @0
    @5
    wcel
    #
    @0
    @6
    wcel
    #
    wo
    #
    wph
    @3
    @0
    @5
    @6
    elun
    @19
    wph
    @3
    @17
    wph
    @3
    wi
    #
    @18
    @17
    @0
    cc0
    wceq
    #
    @20
    @0
    cc0
    elsni
    @21
    wph
    @3
    @21
    wph
    wa
    @1
    cc0
    cP
    cfv
    #
    @2
    clt
    @21
    @1
    @22
    wceq
    wph
    @0
    cc0
    cP
    fveq2
    adantr
    wph
    @22
    @2
    clt
    wbr
    @21
    wph
    cP
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartlt
    adantl
    eqbrtrd
    ex
    syl
    vk
    cv
    #
    cP
    cfv
    #
    @2
    clt
    wbr
    #
    vk
    @6
    wral
    @18
    @3
    wph
    @25
    @3
    vk
    @0
    @6
    vk
    vi
    weq
    @24
    @1
    @2
    clt
    @23
    @0
    cP
    fveq2
    breq1d
    rspccv
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartiltu
    syl11
    jaoi
    com12
    syl5bi
    sylbid
    ralrimiv
end
