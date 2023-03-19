include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "max2.mm"
include "syl2anc.mm"

theorem max2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume max2d.1: |- ( ph -> A e. RR )
  assume max2d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> B <_ if ( A <_ B , B , A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cB
    cA
    cB
    cle
    wbr
    cB
    cA
    cif
    cle
    wbr
    max2d.1
    max2d.2
    cA
    cB
    max2
    syl2anc
end
