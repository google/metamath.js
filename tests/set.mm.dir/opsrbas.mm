include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt10.mm"
include "opsrbaslem.mm"

theorem opsrbas
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> ( Base ` S ) = ( Base ` O ) )

  proof
    wph
    cR
    cS
    cT
    cbs
    cI
    c1
    cO
    opsrbas.s
    opsrbas.o
    opsrbas.t
    df-base
    1nn
    1lt10
    opsrbaslem
end
