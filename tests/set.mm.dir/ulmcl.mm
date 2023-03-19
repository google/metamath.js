include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cuz.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "w3a.mm"
include "cz.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "ulmscl.mm"
include "ulmval.mm"
include "syl.mm"
include "ibi.mm"
include "simp2.mm"
include "rexlimivw.mm"

theorem ulmcl
  let cS: class S
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z


  assert |- ( F ( ~~>u ` S ) G -> G : S --> CC )

  proof
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    vn
    cv
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    cF
    wf
    #
    cS
    cc
    cG
    wf
    #
    vz
    cv
    #
    vk
    cv
    cF
    cfv
    cfv
    @4
    cG
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    vz
    cS
    wral
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    @1
    wrex
    vx
    crp
    wral
    #
    w3a
    #
    vn
    cz
    wrex
    #
    @3
    @0
    @7
    @0
    cS
    cvv
    wcel
    @0
    @7
    wb
    cS
    cF
    cG
    ulmscl
    vx
    vz
    cS
    vj
    vk
    vn
    cF
    cG
    cvv
    ulmval
    syl
    ibi
    @6
    @3
    vn
    cz
    @2
    @3
    @5
    simp2
    rexlimivw
    syl
end
