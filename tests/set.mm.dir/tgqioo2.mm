include "cioo.mm"
include "cq.mm"
include "cxp.mm"
include "cima.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "eqid.mm"
include "tgqioo.mm"
include "3eqtri.mm"
include "a1i.mm"
include "eleqtrd.mm"
include "cvv.mm"
include "wb.mm"
include "iooex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "eltg3.mm"
include "sylib.mm"

theorem tgqioo2
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let vq: setvar q
  assume tgqioo2.1: |- J = ( topGen ` ran (,) )
  assume tgqioo2.2: |- ( ph -> A e. J )

  disjoint A q
  assert |- ( ph -> E. q ( q C_ ( (,) " ( QQ X. QQ ) ) /\ A = U. q ) )

  proof
    wph
    cA
    cioo
    cq
    cq
    cxp
    #
    cima
    #
    ctg
    cfv
    #
    wcel
    #
    vq
    cv
    #
    @1
    wss
    cA
    @4
    cuni
    wceq
    wa
    vq
    wex
    #
    wph
    cA
    cJ
    @2
    tgqioo2.2
    cJ
    @2
    wceq
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    @2
    @2
    tgqioo2.1
    @2
    @2
    eqid
    #
    tgqioo
    @6
    3eqtri
    a1i
    eleqtrd
    @1
    cvv
    wcel
    #
    @3
    @5
    wb
    cioo
    cvv
    wcel
    @7
    iooex
    cioo
    @0
    cvv
    imaexg
    ax-mp
    vq
    cA
    @1
    cvv
    eltg3
    ax-mp
    sylib
end
