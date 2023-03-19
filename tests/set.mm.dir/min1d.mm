include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "min1.mm"
include "syl2anc.mm"

theorem min1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume min1d.1: |- ( ph -> A e. RR )
  assume min1d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> if ( A <_ B , A , B ) <_ A )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cA
    cB
    cif
    cA
    cle
    wbr
    min1d.1
    min1d.2
    cA
    cB
    min1
    syl2anc
end
