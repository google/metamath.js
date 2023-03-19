include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cq.mm"
include "wrex.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "cr.mm"
include "qre.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "eliood.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem qelioo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume qelioo.1: |- ( ph -> A e. RR* )
  assume qelioo.2: |- ( ph -> B e. RR* )
  assume qelioo.3: |- ( ph -> A < B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> E. x e. QQ x e. ( A (,) B ) )

  proof
    wph
    cA
    vx
    cv
    #
    clt
    wbr
    #
    @0
    cB
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @0
    cA
    cB
    cioo
    co
    wcel
    #
    vx
    cq
    wrex
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    @4
    qelioo.1
    qelioo.2
    qelioo.3
    vx
    cA
    cB
    qbtwnxr
    syl3anc
    wph
    @3
    @5
    vx
    cq
    wph
    @0
    cq
    wcel
    #
    wa
    #
    @3
    @5
    @9
    @3
    wa
    cA
    cB
    @0
    wph
    @6
    @8
    @3
    qelioo.1
    ad2antrr
    wph
    @7
    @8
    @3
    qelioo.2
    ad2antrr
    @8
    @0
    cr
    wcel
    wph
    @3
    @0
    qre
    ad2antlr
    @9
    @1
    @2
    simprl
    @9
    @1
    @2
    simprr
    eliood
    ex
    reximdva
    mpd
end
