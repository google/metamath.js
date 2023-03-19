include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "syl6eleqr.mm"

theorem eluzd
  let wph: wff ph
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume eluzd.1: |- Z = ( ZZ>= ` M )
  assume eluzd.2: |- ( ph -> M e. ZZ )
  assume eluzd.3: |- ( ph -> N e. ZZ )
  assume eluzd.4: |- ( ph -> M <_ N )


  assert |- ( ph -> N e. Z )

  proof
    wph
    cN
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    cle
    wbr
    cN
    @0
    wcel
    eluzd.2
    eluzd.3
    eluzd.4
    cM
    cN
    eluz2
    syl3anbrc
    eluzd.1
    syl6eleqr
end
