include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "ltnled.mm"
include "mpbird.mm"

theorem nleltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nleltd.1: |- ( ph -> A e. RR )
  assume nleltd.2: |- ( ph -> B e. RR )
  assume nleltd.3: |- ( ph -> -. B <_ A )


  assert |- ( ph -> A < B )

  proof
    wph
    cA
    cB
    clt
    wbr
    cB
    cA
    cle
    wbr
    wn
    nleltd.3
    wph
    cA
    cB
    nleltd.1
    nleltd.2
    ltnled
    mpbird
end
