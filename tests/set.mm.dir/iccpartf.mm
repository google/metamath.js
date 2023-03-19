include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "crn.mm"
include "cfv.mm"
include "cicc.mm"
include "wss.mm"
include "wf.mm"
include "cn.mm"
include "wcel.mm"
include "ciccp.mm"
include "cxr.mm"
include "cmap.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "iccpart.mm"
include "elmapfn.mm"
include "adantr.mm"
include "syl6bi.mm"
include "sylc.mm"
include "iccpartrn.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem iccpartf
  let wph: wff ph
  let cP: class P
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )


  assert |- ( ph -> P : ( 0 ... M ) --> ( ( P ` 0 ) [,] ( P ` M ) ) )

  proof
    wph
    cP
    cc0
    cM
    cfz
    co
    #
    wfn
    #
    cP
    crn
    cc0
    cP
    cfv
    cM
    cP
    cfv
    cicc
    co
    #
    wss
    @0
    @2
    cP
    wf
    wph
    cM
    cn
    wcel
    #
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @1
    iccpartgtprec.m
    iccpartgtprec.p
    @3
    @4
    cP
    cxr
    @0
    cmap
    co
    wcel
    #
    vi
    cv
    #
    cP
    cfv
    @6
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
    wa
    @1
    cP
    vi
    cM
    iccpart
    @5
    @1
    @7
    cP
    cxr
    @0
    elmapfn
    adantr
    syl6bi
    sylc
    wph
    cP
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartrn
    @0
    @2
    cP
    df-f
    sylanbrc
end
