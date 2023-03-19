include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "lenltd.mm"
include "mpbid.mm"

theorem lensymd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume lensymd.3: |- ( ph -> A <_ B )


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
    lensymd.3
    wph
    cA
    cB
    ltd.1
    ltd.2
    lenltd
    mpbid
end
