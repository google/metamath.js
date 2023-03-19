include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "renegcld.mm"
include "lenegd.mm"
include "recnd.mm"
include "negnegd.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem leneg3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leneg3d.1: |- ( ph -> A e. RR )
  assume leneg3d.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( -u A <_ B <-> -u B <_ A ) )

  proof
    wph
    cA
    cneg
    #
    cB
    cle
    wbr
    cB
    cneg
    #
    @0
    cneg
    #
    cle
    wbr
    @1
    cA
    cle
    wbr
    wph
    @0
    cB
    wph
    cA
    leneg3d.1
    renegcld
    leneg3d.2
    lenegd
    wph
    @2
    cA
    @1
    cle
    wph
    cA
    wph
    cA
    leneg3d.1
    recnd
    negnegd
    breq2d
    bitrd
end
