include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfzo.mm"
include "wceq.mm"
include "wo.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "fzisfzounsn.mm"
include "syl.mm"
include "eleq2d.mm"
include "wb.mm"
include "elun.mm"
include "a1i.mm"
include "velsn.mm"
include "orbi2d.mm"
include "3bitrd.mm"
include "wi.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspccv.mm"
include "iccpartigtl.mm"
include "syl11.mm"
include "wa.mm"
include "iccpartlt.mm"
include "adantl.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "ex.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem iccpartgtl
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
  assert |- ( ph -> A. i e. ( 1 ... M ) ( P ` 0 ) < ( P ` i ) )

  proof
    wph
    cc0
    cP
    cfv
    #
    vi
    cv
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    c1
    cM
    cfz
    co
    #
    wph
    @1
    @4
    wcel
    #
    @1
    c1
    cM
    cfzo
    co
    #
    wcel
    #
    @1
    cM
    wceq
    #
    wo
    #
    @3
    wph
    @5
    @1
    @6
    cM
    csn
    #
    cun
    #
    wcel
    #
    @7
    @1
    @10
    wcel
    #
    wo
    #
    @9
    wph
    @4
    @11
    @1
    wph
    cM
    c1
    cuz
    cfv
    wcel
    #
    @4
    @11
    wceq
    wph
    cM
    cn
    wcel
    @15
    iccpartgtprec.m
    cM
    elnnuz
    sylib
    c1
    cM
    fzisfzounsn
    syl
    eleq2d
    @12
    @14
    wb
    wph
    @1
    @6
    @10
    elun
    a1i
    wph
    @13
    @8
    @7
    @13
    @8
    wb
    wph
    vi
    cM
    velsn
    a1i
    orbi2d
    3bitrd
    @9
    wph
    @3
    @7
    wph
    @3
    wi
    @8
    @0
    vk
    cv
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vk
    @6
    wral
    @7
    @3
    wph
    @18
    @3
    vk
    @1
    @6
    vk
    vi
    weq
    @17
    @2
    @0
    clt
    @16
    @1
    cP
    fveq2
    breq2d
    rspccv
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartigtl
    syl11
    @8
    wph
    @3
    @8
    wph
    wa
    @0
    cM
    cP
    cfv
    #
    @2
    clt
    wph
    @0
    @19
    clt
    wbr
    @8
    wph
    cP
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartlt
    adantl
    @8
    @2
    @19
    wceq
    wph
    @1
    cM
    cP
    fveq2
    adantr
    breqtrrd
    ex
    jaoi
    com12
    sylbid
    ralrimiv
end
