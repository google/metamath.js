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
include "simp1.mm"
include "reximi.mm"

theorem ulmf
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z

  disjoint F n
  disjoint G n
  disjoint S n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint S j
  disjoint S k
  disjoint S x
  disjoint S z
  assert |- ( F ( ~~>u ` S ) G -> E. n e. ZZ F : ( ZZ>= ` n ) --> ( CC ^m S ) )

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
    @2
    vn
    cz
    wrex
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
    @2
    vn
    cz
    @2
    @3
    @5
    simp1
    reximi
    syl
end
