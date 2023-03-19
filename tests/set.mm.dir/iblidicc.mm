include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cibl.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "sylancl.mm"
include "cniccibl.mm"
include "syl3anc.mm"

theorem iblidicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblidicc.a: |- ( ph -> A e. RR )
  assume iblidicc.b: |- ( ph -> B e. RR )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( x e. ( A [,] B ) |-> x ) e. L^1 )

  proof
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    vx
    cA
    cB
    cicc
    co
    #
    vx
    cv
    cmpt
    #
    @2
    cc
    ccncf
    co
    wcel
    #
    @3
    cibl
    wcel
    iblidicc.a
    iblidicc.b
    wph
    @2
    cc
    wss
    cc
    cc
    wss
    @4
    wph
    @2
    cr
    cc
    wph
    @0
    @1
    @2
    cr
    wss
    iblidicc.a
    iblidicc.b
    cA
    cB
    iccssre
    syl2anc
    ax-resscn
    syl6ss
    cc
    ssid
    vx
    @2
    cc
    cncfmptid
    sylancl
    cA
    cB
    @3
    cniccibl
    syl3anc
end
