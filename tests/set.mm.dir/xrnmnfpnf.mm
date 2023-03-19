include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "pm2.53.mm"
include "sylc.mm"

theorem xrnmnfpnf
  let wph: wff ph
  let cA: class A
  assume xrnmnfpnf.1: |- ( ph -> A e. RR* )
  assume xrnmnfpnf.2: |- ( ph -> -. A e. RR )
  assume xrnmnfpnf.3: |- ( ph -> A =/= -oo )


  assert |- ( ph -> A = +oo )

  proof
    wph
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    wo
    #
    @0
    wn
    @1
    wph
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    wa
    @2
    wph
    @3
    @4
    xrnmnfpnf.1
    xrnmnfpnf.3
    jca
    cA
    xrnemnf
    sylib
    xrnmnfpnf.2
    @0
    @1
    pm2.53
    sylc
end
