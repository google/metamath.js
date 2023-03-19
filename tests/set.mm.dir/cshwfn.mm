include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "ccsh.mm"
include "wf.mm"
include "wfn.mm"
include "cshwf.mm"
include "ffn.mm"
include "syl.mm"

theorem cshwfn
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( W cyclShift N ) Fn ( 0 ..^ ( # ` W ) ) )

  proof
    cW
    cV
    cword
    wcel
    cN
    cz
    wcel
    wa
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    cV
    cW
    cN
    ccsh
    co
    #
    wf
    @1
    @0
    wfn
    cV
    cN
    cW
    cshwf
    @0
    cV
    @1
    ffn
    syl
end
