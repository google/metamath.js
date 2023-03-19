include "cvsca.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "6lt10.mm"
include "opsrbaslem.mm"

theorem opsrvsca
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> ( .s ` S ) = ( .s ` O ) )

  proof
    wph
    cR
    cS
    cT
    cvsca
    cI
    c6
    cO
    opsrbas.s
    opsrbas.o
    opsrbas.t
    df-vsca
    6nn
    6lt10
    opsrbaslem
end
