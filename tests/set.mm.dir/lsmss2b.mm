include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "co.mm"
include "wceq.mm"
include "lsmss2.mm"
include "3expia.mm"
include "lsmub2.mm"
include "sseq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem lsmss2b
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


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( U C_ T <-> ( T .(+) U ) = T ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @0
    wcel
    #
    wa
    #
    cU
    cT
    wss
    #
    cT
    cU
    c.po
    co
    #
    cT
    wceq
    #
    @1
    @2
    @4
    @6
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmss2
    3expia
    @3
    cU
    @5
    wss
    @6
    @4
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmub2
    @5
    cT
    cU
    sseq2
    syl5ibcom
    impbid
end
