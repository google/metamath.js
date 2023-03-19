include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cgam.mm"
include "cfv.mm"
include "ce.mm"
include "clgam.mm"
include "ccom.mm"
include "df-gam.mm"
include "fveq1i.mm"
include "wf.mm"
include "wceq.mm"
include "lgamf.mm"
include "fvco3.mm"
include "mpan.mm"
include "syl5req.mm"

theorem eflgam
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( exp ` ( log_G ` A ) ) = ( _G ` A ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    #
    wcel
    #
    cA
    cgam
    cfv
    cA
    ce
    clgam
    ccom
    #
    cfv
    #
    cA
    clgam
    cfv
    ce
    cfv
    #
    cA
    cgam
    @2
    df-gam
    fveq1i
    @0
    cc
    clgam
    wf
    @1
    @3
    @4
    wceq
    lgamf
    @0
    cc
    cA
    ce
    clgam
    fvco3
    mpan
    syl5req
end
