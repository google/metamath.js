include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wb.mm"
include "negelrp.mm"
include "syl.mm"
include "mpbird.mm"

theorem negelrpd
  let wph: wff ph
  let cA: class A
  assume negelrpd.1: |- ( ph -> A e. RR )
  assume negelrpd.2: |- ( ph -> A < 0 )


  assert |- ( ph -> -u A e. RR+ )

  proof
    wph
    cA
    cneg
    crp
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    negelrpd.2
    wph
    cA
    cr
    wcel
    @0
    @1
    wb
    negelrpd.1
    cA
    negelrp
    syl
    mpbird
end
