include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "lenltd.mm"
include "mpbird.mm"

theorem nltled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume nltled.1: |- ( ph -> -. B < A )


  assert |- ( ph -> A <_ B )

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
    nltled.1
    wph
    cA
    cB
    ltd.1
    ltd.2
    lenltd
    mpbird
end
