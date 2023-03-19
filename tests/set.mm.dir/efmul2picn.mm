include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "efcn.mm"
include "a1i.mm"
include "wss.mm"
include "cmpt.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "cncfrss.mm"
include "syl.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "mulcncf.mm"
include "cncfmpt1f.mm"

theorem efmul2picn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume efmul2picn.1: |- ( ph -> ( x e. A |-> B ) e. ( A -cn-> CC ) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. B ) ) ) e. ( A -cn-> CC ) )

  proof
    wph
    vx
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cB
    cmul
    co
    ce
    cA
    ce
    cc
    cc
    ccncf
    co
    wcel
    wph
    efcn
    a1i
    wph
    vx
    @1
    cB
    cA
    wph
    @1
    cc
    wcel
    #
    cA
    cc
    wss
    #
    cc
    cc
    wss
    #
    vx
    cA
    @1
    cmpt
    cA
    cc
    ccncf
    co
    #
    wcel
    @2
    wph
    ci
    @0
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    a1i
    wph
    vx
    cA
    cB
    cmpt
    #
    @5
    wcel
    @3
    efmul2picn.1
    cA
    cc
    @6
    cncfrss
    syl
    @4
    wph
    cc
    ssid
    a1i
    vx
    @1
    cA
    cc
    cncfmptc
    syl3anc
    efmul2picn.1
    mulcncf
    cncfmpt1f
end
