include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wi.mm"
include "ltle.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem ltled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume ltled.1: |- ( ph -> A < B )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    ltled.1
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wi
    ltd.1
    ltd.2
    cA
    cB
    ltle
    syl2anc
    mpd
end
