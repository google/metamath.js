include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "min2.mm"
include "syl2anc.mm"

theorem min2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume min2d.1: |- ( ph -> A e. RR )
  assume min2d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> if ( A <_ B , A , B ) <_ B )

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
    cB
    cle
    wbr
    min2d.1
    min2d.2
    cA
    cB
    min2
    syl2anc
end
