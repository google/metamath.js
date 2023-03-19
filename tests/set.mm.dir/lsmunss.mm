include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "lsmub1.mm"
include "lsmub2.mm"
include "unssd.mm"

theorem lsmunss
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let cR: class R
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( T u. U ) C_ ( T .(+) U ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    cU
    @0
    wcel
    wa
    cT
    cU
    cT
    cU
    c.po
    co
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmub1
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmub2
    unssd
end
