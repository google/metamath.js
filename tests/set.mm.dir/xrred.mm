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
include "neneqd.mm"
include "pm2.53.mm"
include "con1d.mm"
include "sylc.mm"

theorem xrred
  let wph: wff ph
  let cA: class A
  assume xrred.1: |- ( ph -> A e. RR* )
  assume xrred.2: |- ( ph -> A =/= -oo )
  assume xrred.3: |- ( ph -> A =/= +oo )


  assert |- ( ph -> A e. RR )

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
    @1
    wn
    @0
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
    xrred.1
    xrred.2
    jca
    cA
    xrnemnf
    sylib
    wph
    cA
    cpnf
    xrred.3
    neneqd
    @2
    @0
    @1
    @0
    @1
    pm2.53
    con1d
    sylc
end
