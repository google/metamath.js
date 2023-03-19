include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "neneqd.mm"
include "cpr.mm"
include "wcel.mm"
include "wo.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "elind.mm"
include "cconn.mm"
include "ctop.mm"
include "isconn.mm"
include "simprbi.mm"
include "syl.mm"
include "eleqtrd.mm"
include "elpri.mm"
include "ord.mm"
include "mpd.mm"

theorem connclo
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume isconn.1: |- X = U. J
  assume connclo.1: |- ( ph -> J e. Conn )
  assume connclo.2: |- ( ph -> A e. J )
  assume connclo.3: |- ( ph -> A =/= (/) )
  assume connclo.4: |- ( ph -> A e. ( Clsd ` J ) )


  assert |- ( ph -> A = X )

  proof
    wph
    cA
    c0
    wceq
    #
    wn
    cA
    cX
    wceq
    #
    wph
    cA
    c0
    connclo.3
    neneqd
    wph
    @0
    @1
    wph
    cA
    c0
    cX
    cpr
    #
    wcel
    @0
    @1
    wo
    wph
    cA
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    @2
    wph
    cJ
    @3
    cA
    connclo.2
    connclo.4
    elind
    wph
    cJ
    cconn
    wcel
    #
    @4
    @2
    wceq
    #
    connclo.1
    @5
    cJ
    ctop
    wcel
    @6
    cJ
    cX
    isconn.1
    isconn
    simprbi
    syl
    eleqtrd
    cA
    c0
    cX
    elpri
    syl
    ord
    mpd
end
