include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "max1.mm"
include "syl2anc.mm"

theorem max1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume max1d.1: |- ( ph -> A e. RR )
  assume max1d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> A <_ if ( A <_ B , B , A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cA
    cB
    cle
    wbr
    cB
    cA
    cif
    cle
    wbr
    max1d.1
    max1d.2
    cA
    cB
    max1
    syl2anc
end
