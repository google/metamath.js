include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "cxr.mm"
include "cpnf.mm"
include "wne.mm"
include "wa.mm"
include "jca.mm"
include "xrnepnf.mm"
include "sylib.mm"
include "pm2.53.mm"
include "sylc.mm"

theorem xrnpnfmnf
  let wph: wff ph
  let cA: class A
  assume xrnpnfmnf.1: |- ( ph -> A e. RR* )
  assume xrnpnfmnf.2: |- ( ph -> -. A e. RR )
  assume xrnpnfmnf.3: |- ( ph -> A =/= +oo )


  assert |- ( ph -> A = -oo )

  proof
    wph
    cA
    cr
    wcel
    #
    cA
    cmnf
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
    cpnf
    wne
    #
    wa
    @2
    wph
    @3
    @4
    xrnpnfmnf.1
    xrnpnfmnf.3
    jca
    cA
    xrnepnf
    sylib
    xrnpnfmnf.2
    @0
    @1
    pm2.53
    sylc
end
