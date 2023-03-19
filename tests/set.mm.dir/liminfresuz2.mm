include "cr.mm"
include "cres.mm"
include "cdm.mm"
include "cz.mm"
include "wss.mm"
include "dmresss.mm"
include "a1i.mm"
include "sstrd.mm"
include "liminfresuz.mm"

theorem liminfresuz2
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume liminfresuz2.1: |- ( ph -> M e. ZZ )
  assume liminfresuz2.2: |- Z = ( ZZ>= ` M )
  assume liminfresuz2.3: |- ( ph -> F e. V )
  assume liminfresuz2.4: |- ( ph -> dom F C_ ZZ )


  assert |- ( ph -> ( liminf ` ( F |` Z ) ) = ( liminf ` F ) )

  proof
    wph
    cF
    cM
    cV
    cZ
    liminfresuz2.1
    liminfresuz2.2
    liminfresuz2.3
    wph
    cF
    cr
    cres
    cdm
    #
    cF
    cdm
    #
    cz
    @0
    @1
    wss
    wph
    cF
    cr
    dmresss
    a1i
    liminfresuz2.4
    sstrd
    liminfresuz
end
