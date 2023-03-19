include "cvv.mm"
include "wcel.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "cvtx.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "co.mm"
include "crab.mm"
include "cmpt2.mm"
include "fveq2.mm"
include "eqidd.mm"
include "oveq2.mm"
include "rabeqdv.mm"
include "mpt2eq123dv.mm"
include "df-clwwlknon.mm"
include "fvex.mm"
include "nn0ex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "mpt20.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem clwwlknonmpt2
  let vw: setvar w
  let vv: setvar v
  let vn: setvar n
  let cG: class G
  let vg: setvar g

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint G g
  disjoint g n
  disjoint g v
  disjoint g w
  assert |- ( ClWWalksNOn ` G ) = ( v e. ( Vtx ` G ) , n e. NN0 |-> { w e. ( n ClWWalksN G ) | ( w ` 0 ) = v } )

  proof
    cG
    cvv
    wcel
    #
    cG
    cclwwlknon
    cfv
    #
    vv
    vn
    cG
    cvtx
    cfv
    #
    cn0
    cc0
    vw
    cv
    cfv
    vv
    cv
    wceq
    #
    vw
    vn
    cv
    #
    cG
    cclwwlkn
    co
    #
    crab
    #
    cmpt2
    #
    wceq
    vg
    cG
    vv
    vn
    vg
    cv
    #
    cvtx
    cfv
    #
    cn0
    @3
    vw
    @4
    @8
    cclwwlkn
    co
    #
    crab
    #
    cmpt2
    @7
    cvv
    cclwwlknon
    @8
    cG
    wceq
    #
    vv
    vn
    @9
    cn0
    @11
    @2
    cn0
    @6
    @8
    cG
    cvtx
    fveq2
    @12
    cn0
    eqidd
    @12
    @3
    vw
    @10
    @5
    @8
    cG
    @4
    cclwwlkn
    oveq2
    rabeqdv
    mpt2eq123dv
    vw
    vv
    vg
    vn
    df-clwwlknon
    vv
    vn
    @2
    cn0
    @6
    cG
    cvtx
    fvex
    nn0ex
    mpt2ex
    fvmpt
    @0
    wn
    #
    @1
    c0
    @7
    cG
    cclwwlknon
    fvprc
    @13
    @7
    vv
    vn
    c0
    cn0
    @6
    cmpt2
    c0
    @13
    vv
    vn
    @2
    cn0
    @6
    c0
    cn0
    @6
    cG
    cvtx
    fvprc
    @13
    cn0
    eqidd
    @13
    @6
    eqidd
    mpt2eq123dv
    vv
    vn
    cn0
    @6
    mpt20
    syl6req
    eqtrd
    pm2.61i
end
