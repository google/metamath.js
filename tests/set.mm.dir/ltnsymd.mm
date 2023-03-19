include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "ltled.mm"
include "lenltd.mm"
include "mpbid.mm"

theorem ltnsymd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume ltled.1: |- ( ph -> A < B )


  assert |- ( ph -> -. B < A )

  proof
    wph
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    wn
    wph
    cA
    cB
    ltd.1
    ltd.2
    ltled.1
    ltled
    wph
    cA
    cB
    ltd.1
    ltd.2
    lenltd
    mpbid
end
