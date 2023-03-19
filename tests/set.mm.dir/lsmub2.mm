include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cbs.mm"
include "wss.mm"
include "co.mm"
include "subgsubm.mm"
include "eqid.mm"
include "subgss.mm"
include "lsmub2x.mm"
include "syl2an.mm"

theorem lsmub2
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


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> U C_ ( T .(+) U ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    cT
    cG
    csubmnd
    cfv
    wcel
    cU
    cG
    cbs
    cfv
    #
    wss
    cU
    cT
    cU
    c.po
    co
    wss
    cU
    @0
    wcel
    cT
    cG
    subgsubm
    @1
    cU
    cG
    @1
    eqid
    #
    subgss
    @1
    c.po
    cT
    cU
    cG
    @2
    lsmub1.p
    lsmub2x
    syl2an
end
