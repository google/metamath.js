include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "lveclmod.mm"
include "lsslmod.mm"
include "sylan.mm"
include "wceq.mm"
include "eqid.mm"
include "resssca.mm"
include "adantl.mm"
include "lvecdrng.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "islvec.mm"
include "sylanbrc.mm"

theorem lsslvec
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  assume lsslvec.x: |- X = ( W |`s U )
  assume lsslvec.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LVec /\ U e. S ) -> X e. LVec )

  proof
    cW
    clvec
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    clmod
    wcel
    #
    cX
    csca
    cfv
    #
    cdr
    wcel
    cX
    clvec
    wcel
    @0
    cW
    clmod
    wcel
    @1
    @3
    cW
    lveclmod
    cS
    cU
    cW
    cX
    lsslvec.x
    lsslvec.s
    lsslmod
    sylan
    @2
    cW
    csca
    cfv
    #
    @4
    cdr
    @1
    @5
    @4
    wceq
    @0
    cU
    @5
    cW
    cX
    cS
    lsslvec.x
    @5
    eqid
    #
    resssca
    adantl
    @0
    @5
    cdr
    wcel
    @1
    @5
    cW
    @6
    lvecdrng
    adantr
    eqeltrrd
    @4
    cX
    @4
    eqid
    islvec
    sylanbrc
end
