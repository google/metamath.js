include "wcel.mm"
include "cz.mm"
include "eluzelz2.mm"
include "syl.mm"

theorem eluzelz2d
  let wph: wff ph
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume eluzelz2d.1: |- Z = ( ZZ>= ` M )
  assume eluzelz2d.2: |- ( ph -> N e. Z )


  assert |- ( ph -> N e. ZZ )

  proof
    wph
    cN
    cZ
    wcel
    cN
    cz
    wcel
    eluzelz2d.2
    cM
    cN
    cZ
    eluzelz2d.1
    eluzelz2
    syl
end
