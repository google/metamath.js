include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "cmpt2.mm"
include "cvtx.mm"
include "clwwlknonmpt2.mm"
include "eqcomi.mm"
include "eqid.mm"
include "mpt2eq123i.mm"
include "eqtri.mm"
include "oveqi.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "rabeqdv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem clwwlknonOLD
  let vw: setvar w
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v
  assume clwwlknon.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint N w
  disjoint X w
  disjoint G g
  disjoint G n
  disjoint G v
  disjoint g n
  disjoint g v
  disjoint g w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint X n
  disjoint X v
  disjoint V n
  disjoint V v
  assert |- ( ( X e. V /\ N e. NN0 ) -> ( X ( ClWWalksNOn ` G ) N ) = { w e. ( N ClWWalksN G ) | ( w ` 0 ) = X } )

  proof
    cX
    cV
    wcel
    cN
    cn0
    wcel
    wa
    cX
    cN
    cG
    cclwwlknon
    cfv
    #
    co
    cX
    cN
    vv
    vn
    cV
    cn0
    cc0
    vw
    cv
    cfv
    #
    vv
    cv
    #
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
    co
    @1
    cX
    wceq
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    @0
    @7
    cX
    cN
    @0
    vv
    vn
    cG
    cvtx
    cfv
    #
    cn0
    @6
    cmpt2
    @7
    vw
    vv
    vn
    cG
    clwwlknonmpt2
    vv
    vn
    @11
    cn0
    @6
    cV
    cn0
    @6
    cV
    @11
    clwwlknon.v
    eqcomi
    cn0
    eqid
    @6
    eqid
    mpt2eq123i
    eqtri
    oveqi
    vv
    vn
    cX
    cN
    cV
    cn0
    @6
    @10
    @7
    @8
    vw
    @5
    crab
    @2
    cX
    wceq
    @3
    @8
    vw
    @5
    @2
    cX
    @1
    eqeq2
    rabbidv
    @4
    cN
    wceq
    @8
    vw
    @5
    @9
    @4
    cN
    cG
    cclwwlkn
    oveq1
    rabeqdv
    @7
    eqid
    @8
    vw
    @9
    cN
    cG
    cclwwlkn
    ovex
    rabex
    ovmpt2
    syl5eq
end
