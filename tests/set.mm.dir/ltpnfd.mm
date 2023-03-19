include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "ltpnf.mm"
include "syl.mm"

theorem ltpnfd
  let wph: wff ph
  let cA: class A
  assume ltpnfd.a: |- ( ph -> A e. RR )


  assert |- ( ph -> A < +oo )

  proof
    wph
    cA
    cr
    wcel
    cA
    cpnf
    clt
    wbr
    ltpnfd.a
    cA
    ltpnf
    syl
end
