include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "renegcld.mm"
include "lenegd.mm"
include "recnd.mm"
include "negnegd.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem leneg2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leneg2d.1: |- ( ph -> A e. RR )
  assume leneg2d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A <_ -u B <-> B <_ -u A ) )

  proof
    wph
    cA
    cB
    cneg
    #
    cle
    wbr
    @0
    cneg
    #
    cA
    cneg
    #
    cle
    wbr
    cB
    @2
    cle
    wbr
    wph
    cA
    @0
    leneg2d.1
    wph
    cB
    leneg2d.2
    renegcld
    lenegd
    wph
    @1
    cB
    @2
    cle
    wph
    cB
    wph
    cB
    leneg2d.2
    recnd
    negnegd
    breq1d
    bitrd
end
