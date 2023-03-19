include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "simpll.mm"
include "eqid.mm"
include "lssel.mm"
include "ad2ant2lr.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simplr.mm"
include "lmod1cl.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "lsscl.mm"
include "syl13anc.mm"
include "eqeltrrd.mm"

theorem lssvacl
  let c.pl: class .+
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lssvacl.p: |- .+ = ( +g ` W )
  assume lssvacl.s: |- S = ( LSubSp ` W )


  assert |- ( ( ( W e. LMod /\ U e. S ) /\ ( X e. U /\ Y e. U ) ) -> ( X .+ Y ) e. U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    #
    wa
    #
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    cX
    cW
    cvsca
    cfv
    #
    co
    #
    cY
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    cU
    @6
    @10
    cX
    cY
    c.pl
    @6
    @0
    cX
    cW
    cbs
    cfv
    #
    wcel
    #
    @10
    cX
    wceq
    @0
    @1
    @5
    simpll
    @1
    @3
    @13
    @0
    @4
    cS
    cU
    @12
    cW
    cX
    @12
    eqid
    #
    lssvacl.s
    lssel
    ad2ant2lr
    @9
    @8
    @7
    @12
    cW
    cX
    @14
    @7
    eqid
    #
    @9
    eqid
    #
    @8
    eqid
    #
    lmodvs1
    syl2anc
    oveq1d
    @6
    @1
    @8
    @7
    cbs
    cfv
    #
    wcel
    #
    @3
    @4
    @11
    cU
    wcel
    @0
    @1
    @5
    simplr
    @0
    @19
    @1
    @5
    @8
    @7
    @18
    cW
    @15
    @18
    eqid
    #
    @17
    lmod1cl
    ad2antrr
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    @18
    c.pl
    cS
    @9
    cU
    @7
    cW
    cX
    cY
    @8
    @15
    @20
    lssvacl.p
    @16
    lssvacl.s
    lsscl
    syl13anc
    eqeltrrd
end
