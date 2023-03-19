include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "cmulr.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "3ad2ant1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lfli.mm"
include "syl113anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "crg.mm"
include "lmodring.mm"
include "lflcl.mm"
include "3adant3r.mm"
include "ringlidm.mm"
include "3eqtr3d.mm"

theorem lfladd
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lfladd.d: |- D = ( Scalar ` W )
  assume lfladd.p: |- .+^ = ( +g ` D )
  assume lfladd.v: |- V = ( Base ` W )
  assume lfladd.a: |- .+ = ( +g ` W )
  assume lfladd.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. LMod /\ G e. F /\ ( X e. V /\ Y e. V ) ) -> ( G ` ( X .+ Y ) ) = ( ( G ` X ) .+^ ( G ` Y ) ) )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cD
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
    cG
    cfv
    #
    @6
    cX
    cG
    cfv
    #
    cD
    cmulr
    cfv
    #
    co
    #
    cY
    cG
    cfv
    #
    c.pd
    co
    #
    cX
    cY
    c.pl
    co
    #
    cG
    cfv
    @11
    @14
    c.pd
    co
    @5
    @0
    @1
    @6
    cD
    cbs
    cfv
    #
    wcel
    #
    @2
    @3
    @10
    @15
    wceq
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @4
    simp2
    @0
    @1
    @18
    @4
    @6
    cD
    @17
    cW
    lfladd.d
    @17
    eqid
    #
    @6
    eqid
    #
    lmod1cl
    3ad2ant1
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @2
    @3
    simp3r
    cD
    c.pl
    c.pd
    @6
    @7
    @12
    cF
    cG
    @17
    cV
    cW
    cX
    cY
    clmod
    lfladd.v
    lfladd.a
    lfladd.d
    @7
    eqid
    #
    @20
    lfladd.p
    @12
    eqid
    #
    lfladd.f
    lfli
    syl113anc
    @5
    @9
    @16
    cG
    @5
    @8
    cX
    cY
    c.pl
    @5
    @0
    @2
    @8
    cX
    wceq
    @19
    @22
    @7
    @6
    cD
    cV
    cW
    cX
    lfladd.v
    lfladd.d
    @23
    @21
    lmodvs1
    syl2anc
    oveq1d
    fveq2d
    @5
    @13
    @11
    @14
    c.pd
    @5
    cD
    crg
    wcel
    #
    @11
    @17
    wcel
    #
    @13
    @11
    wceq
    @0
    @1
    @25
    @4
    cD
    cW
    lfladd.d
    lmodring
    3ad2ant1
    @0
    @1
    @2
    @26
    @3
    cD
    cF
    cG
    @17
    cV
    cW
    cX
    clmod
    lfladd.d
    @20
    lfladd.v
    lfladd.f
    lflcl
    3adant3r
    @17
    cD
    @12
    @6
    @11
    @20
    @24
    @21
    ringlidm
    syl2anc
    oveq1d
    3eqtr3d
end
