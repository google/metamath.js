include "crest.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "a1i.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "elrest.mm"
include "mpbird.mm"

theorem elrestd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume elrestd.1: |- ( ph -> J e. V )
  assume elrestd.2: |- ( ph -> B e. W )
  assume elrestd.3: |- ( ph -> X e. J )
  assume elrestd.4: |- A = ( X i^i B )


  assert |- ( ph -> A e. ( J |`t B ) )

  proof
    wph
    cA
    cJ
    cB
    crest
    co
    wcel
    #
    cA
    vx
    cv
    #
    cB
    cin
    #
    wceq
    #
    vx
    cJ
    wrex
    #
    wph
    cX
    cJ
    wcel
    cA
    cX
    cB
    cin
    #
    wceq
    #
    @4
    elrestd.3
    @6
    wph
    elrestd.4
    a1i
    @3
    @6
    vx
    cX
    cJ
    @1
    cX
    wceq
    @2
    @5
    cA
    @1
    cX
    cB
    ineq1
    eqeq2d
    rspcev
    syl2anc
    wph
    cJ
    cV
    wcel
    cB
    cW
    wcel
    @0
    @4
    wb
    elrestd.1
    elrestd.2
    vx
    cA
    cB
    cJ
    cV
    cW
    elrest
    syl2anc
    mpbird
end
