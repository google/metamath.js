include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cuz.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "cpm.mm"
include "wcel.mm"
include "ulmf.mm"
include "wss.mm"
include "uzssz.mm"
include "cvv.mm"
include "wa.mm"
include "ovex.mm"
include "zex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "rexlimivw.mm"
include "syl.mm"

theorem ulmpm
  let cS: class S
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z


  assert |- ( F ( ~~>u ` S ) G -> F e. ( ( CC ^m S ) ^pm ZZ ) )

  proof
    cF
    cG
    cS
    culm
    cfv
    wbr
    vn
    cv
    #
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    vn
    cz
    wrex
    cF
    @2
    cz
    cpm
    co
    wcel
    #
    cS
    vn
    cF
    cG
    ulmf
    @3
    @4
    vn
    cz
    @3
    @1
    cz
    wss
    #
    @4
    @0
    uzssz
    @2
    cvv
    wcel
    cz
    cvv
    wcel
    @3
    @5
    wa
    @4
    cc
    cS
    cmap
    ovex
    zex
    @2
    cz
    @1
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    mpan2
    rexlimivw
    syl
end
