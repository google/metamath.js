include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt10.mm"
include "opsrbaslem.mm"

theorem opsrplusg
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> ( +g ` S ) = ( +g ` O ) )

  proof
    wph
    cR
    cS
    cT
    cplusg
    cI
    c2
    cO
    opsrbas.s
    opsrbas.o
    opsrbas.t
    df-plusg
    2nn
    2lt10
    opsrbaslem
end
