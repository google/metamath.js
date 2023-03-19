include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cn0.mm"
include "wcel.mm"
include "crctiswlk.mm"
include "chash.mm"
include "wlkcl.mm"
include "syl5eqel.mm"
include "3syl.mm"

theorem crctcshlem1
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )


  assert |- ( ph -> N e. NN0 )

  proof
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cN
    cn0
    wcel
    crctcsh.d
    cP
    cF
    cG
    crctiswlk
    @0
    cN
    cF
    chash
    cfv
    cn0
    crctcsh.n
    cP
    cF
    cG
    wlkcl
    syl5eqel
    3syl
end
