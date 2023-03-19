include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "clmhm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "wa.mm"
include "ccom.mm"
include "eqid.mm"
include "islmim.mm"
include "lmhmco.mm"
include "ad2ant2r.mm"
include "f1oco.mm"
include "ad2ant2l.mm"
include "sylanbrc.mm"
include "syl2anb.mm"

theorem lmimco
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( F e. ( S LMIso T ) /\ G e. ( R LMIso S ) ) -> ( F o. G ) e. ( R LMIso T ) )

  proof
    cF
    cS
    cT
    clmim
    co
    wcel
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cF
    wf1o
    #
    wa
    #
    cG
    cR
    cS
    clmhm
    co
    wcel
    #
    cR
    cbs
    cfv
    #
    @1
    cG
    wf1o
    #
    wa
    #
    cF
    cG
    ccom
    #
    cR
    cT
    clmim
    co
    wcel
    #
    cG
    cR
    cS
    clmim
    co
    wcel
    @1
    @2
    cS
    cT
    cF
    @1
    eqid
    #
    @2
    eqid
    #
    islmim
    @6
    @1
    cR
    cS
    cG
    @6
    eqid
    #
    @11
    islmim
    @4
    @8
    wa
    @9
    cR
    cT
    clmhm
    co
    wcel
    #
    @6
    @2
    @9
    wf1o
    #
    @10
    @0
    @5
    @14
    @3
    @7
    cF
    cG
    cR
    cS
    cT
    lmhmco
    ad2ant2r
    @3
    @7
    @15
    @0
    @5
    @6
    @1
    @2
    cF
    cG
    f1oco
    ad2ant2l
    @6
    @2
    cR
    cT
    @9
    @13
    @12
    islmim
    sylanbrc
    syl2anb
end
