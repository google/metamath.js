include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cres.mm"
include "cop.mm"
include "csubstr.mm"
include "swrd0val.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "swrd0len.mm"
include "eqtrd.mm"

theorem wlkreslem0
  let cS: class S
  let cF: class F
  let cN: class N


  assert |- ( ( F e. Word S /\ N e. ( 0 ... ( # ` F ) ) ) -> ( # ` ( F |` ( 0 ..^ N ) ) ) = N )

  proof
    cF
    cS
    cword
    wcel
    cN
    cc0
    cF
    chash
    cfv
    cfz
    co
    wcel
    wa
    #
    cF
    cc0
    cN
    cfzo
    co
    cres
    #
    chash
    cfv
    cF
    cc0
    cN
    cop
    csubstr
    co
    #
    chash
    cfv
    cN
    @0
    @1
    @2
    chash
    @0
    @2
    @1
    cS
    cF
    cN
    swrd0val
    eqcomd
    fveq2d
    cS
    cF
    cN
    swrd0len
    eqtrd
end
