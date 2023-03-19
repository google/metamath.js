include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "elrp.mm"
include "sylanbrc.mm"

theorem elrpd
  let wph: wff ph
  let cA: class A
  assume elrpd.1: |- ( ph -> A e. RR )
  assume elrpd.2: |- ( ph -> 0 < A )


  assert |- ( ph -> A e. RR+ )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    crp
    wcel
    elrpd.1
    elrpd.2
    cA
    elrp
    sylanbrc
end
