include "csca.mm"
include "cfv.mm"
include "psrsca.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "5lt10.mm"
include "opsrbaslem.mm"
include "eqtrd.mm"

theorem opsrsca
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  let cV: class V
  let cW: class W
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrsca.i: |- ( ph -> I e. V )
  assume opsrsca.r: |- ( ph -> R e. W )


  assert |- ( ph -> R = ( Scalar ` O ) )

  proof
    wph
    cR
    cS
    csca
    cfv
    cO
    csca
    cfv
    wph
    cR
    cS
    cI
    cV
    cW
    opsrbas.s
    opsrsca.i
    opsrsca.r
    psrsca
    wph
    cR
    cS
    cT
    csca
    cI
    c5
    cO
    opsrbas.s
    opsrbas.o
    opsrbas.t
    df-sca
    5nn
    5lt10
    opsrbaslem
    eqtrd
end
