include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "csubmnd.mm"
include "co.mm"
include "eqid.mm"
include "subgss.mm"
include "subgsubm.mm"
include "lsmub1x.mm"
include "syl2an.mm"

theorem lsmub1
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


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> T C_ ( T .(+) U ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    cT
    cG
    cbs
    cfv
    #
    wss
    cU
    cG
    csubmnd
    cfv
    wcel
    cT
    cT
    cU
    c.po
    co
    wss
    cU
    @0
    wcel
    @1
    cT
    cG
    @1
    eqid
    #
    subgss
    cU
    cG
    subgsubm
    @1
    c.po
    cT
    cU
    cG
    @2
    lsmub1.p
    lsmub1x
    syl2an
end
