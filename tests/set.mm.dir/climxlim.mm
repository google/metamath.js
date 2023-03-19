include "clsxlim.mm"
include "wbr.mm"
include "cli.mm"
include "cr.mm"
include "cv.mm"
include "ffvelrnda.mm"
include "climrecl.mm"
include "xlimclim.mm"
include "mpbird.mm"

theorem climxlim
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climxlim.m: |- ( ph -> M e. ZZ )
  assume climxlim.z: |- Z = ( ZZ>= ` M )
  assume climxlim.f: |- ( ph -> F : Z --> RR )
  assume climxlim.c: |- ( ph -> F ~~> A )


  assert |- ( ph -> F ~~>* A )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    cF
    cA
    cli
    wbr
    climxlim.c
    wph
    cA
    cF
    cM
    cZ
    climxlim.m
    climxlim.z
    climxlim.f
    wph
    cA
    vk
    cF
    cM
    cZ
    climxlim.z
    climxlim.m
    climxlim.c
    wph
    cZ
    cr
    vk
    cv
    cF
    climxlim.f
    ffvelrnda
    climrecl
    xlimclim
    mpbird
end
