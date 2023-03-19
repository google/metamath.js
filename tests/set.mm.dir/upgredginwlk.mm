include "cupgr.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wi.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "edginwlk.mm"
include "3expia.mm"
include "sylan.mm"

theorem upgredginwlk
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  assume edginwlk.i: |- I = ( iEdg ` G )
  assume edginwlk.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UPGraph /\ F e. Word dom I ) -> ( K e. ( 0 ..^ ( # ` F ) ) -> ( I ` ( F ` K ) ) e. E ) )

  proof
    cG
    cupgr
    wcel
    #
    cI
    wfun
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cK
    cc0
    cF
    chash
    cfv
    cfzo
    co
    wcel
    #
    cK
    cF
    cfv
    cI
    cfv
    cE
    wcel
    #
    wi
    @0
    cG
    cuhgr
    wcel
    @1
    cG
    upgruhgr
    cI
    cG
    edginwlk.i
    uhgrfun
    syl
    @1
    @2
    @3
    @4
    cE
    cF
    cG
    cI
    cK
    edginwlk.i
    edginwlk.e
    edginwlk
    3expia
    sylan
end
