include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cxr.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "ciccp.mm"
include "wa.mm"
include "cn.mm"
include "wb.mm"
include "iccpart.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "ffvelrnd.mm"

theorem iccpartxr
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )
  assume iccpartxr.i: |- ( ph -> I e. ( 0 ... M ) )


  assert |- ( ph -> ( P ` I ) e. RR* )

  proof
    wph
    cc0
    cM
    cfz
    co
    #
    cxr
    cI
    cP
    wph
    cP
    cxr
    @0
    cmap
    co
    wcel
    #
    @0
    cxr
    cP
    wf
    wph
    @1
    vi
    cv
    #
    cP
    cfv
    @2
    c1
    caddc
    co
    cP
    cfv
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    wral
    #
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @1
    @3
    wa
    #
    iccpartgtprec.p
    wph
    cM
    cn
    wcel
    @4
    @5
    wb
    iccpartgtprec.m
    cP
    vi
    cM
    iccpart
    syl
    mpbid
    simpld
    cP
    cxr
    @0
    elmapi
    syl
    iccpartxr.i
    ffvelrnd
end
