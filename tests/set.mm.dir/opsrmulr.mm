include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "3lt10.mm"
include "opsrbaslem.mm"

theorem opsrmulr
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> ( .r ` S ) = ( .r ` O ) )

  proof
    wph
    cR
    cS
    cT
    cmulr
    cI
    c3
    cO
    opsrbas.s
    opsrbas.o
    opsrbas.t
    df-mulr
    3nn
    3lt10
    opsrbaslem
end
