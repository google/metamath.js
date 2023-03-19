include "cr.mm"
include "cres.mm"
include "cdm.mm"
include "cz.mm"
include "wss.mm"
include "dmresss.mm"
include "a1i.mm"
include "sstrd.mm"
include "limsupresuz.mm"

theorem limsupresuz2
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume limsupresuz2.1: |- ( ph -> M e. ZZ )
  assume limsupresuz2.2: |- Z = ( ZZ>= ` M )
  assume limsupresuz2.3: |- ( ph -> F e. V )
  assume limsupresuz2.4: |- ( ph -> dom F C_ ZZ )


  assert |- ( ph -> ( limsup ` ( F |` Z ) ) = ( limsup ` F ) )

  proof
    wph
    cF
    cM
    cV
    cZ
    limsupresuz2.1
    limsupresuz2.2
    limsupresuz2.3
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
    limsupresuz2.4
    sstrd
    limsupresuz
end
