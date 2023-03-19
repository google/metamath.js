include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wi.mm"
include "0re.mm"
include "recld.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "wne.mm"
include "crp.mm"
include "wn.mm"
include "cc.mm"
include "wceq.mm"
include "reim.mm"
include "syl.mm"
include "gt0ne0d.mm"
include "eqnetrrd.mm"
include "rpre.mm"
include "reim0d.mm"
include "necon3ai.mm"
include "eqsqrtd.mm"

theorem eqsqrt2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume eqsqrtd.1: |- ( ph -> A e. CC )
  assume eqsqrtd.2: |- ( ph -> B e. CC )
  assume eqsqrtd.3: |- ( ph -> ( A ^ 2 ) = B )
  assume eqsqrt2d.4: |- ( ph -> 0 < ( Re ` A ) )


  assert |- ( ph -> A = ( sqrt ` B ) )

  proof
    wph
    cA
    cB
    eqsqrtd.1
    eqsqrtd.2
    eqsqrtd.3
    wph
    cc0
    cA
    cre
    cfv
    #
    clt
    wbr
    #
    cc0
    @0
    cle
    wbr
    #
    eqsqrt2d.4
    wph
    cc0
    cr
    wcel
    @0
    cr
    wcel
    @1
    @2
    wi
    0re
    wph
    cA
    eqsqrtd.1
    recld
    cc0
    @0
    ltle
    sylancr
    mpd
    wph
    ci
    cA
    cmul
    co
    #
    cim
    cfv
    #
    cc0
    wne
    @3
    crp
    wcel
    #
    wn
    wph
    @0
    @4
    cc0
    wph
    cA
    cc
    wcel
    @0
    @4
    wceq
    eqsqrtd.1
    cA
    reim
    syl
    wph
    @0
    eqsqrt2d.4
    gt0ne0d
    eqnetrrd
    @5
    @4
    cc0
    @5
    @3
    @3
    rpre
    reim0d
    necon3ai
    syl
    eqsqrtd
end
