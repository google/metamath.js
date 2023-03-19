include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "lt2sq.mm"
include "syl22anc.mm"

theorem lt2sqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqcld.1: |- ( ph -> A e. RR )
  assume lt2sqd.2: |- ( ph -> B e. RR )
  assume lt2sqd.3: |- ( ph -> 0 <_ A )
  assume lt2sqd.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> ( A < B <-> ( A ^ 2 ) < ( B ^ 2 ) ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cA
    cB
    clt
    wbr
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    clt
    wbr
    wb
    resqcld.1
    lt2sqd.3
    lt2sqd.2
    lt2sqd.4
    cA
    cB
    lt2sq
    syl22anc
end
