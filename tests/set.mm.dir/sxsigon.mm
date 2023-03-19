include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "csx.mm"
include "co.mm"
include "cxp.mm"
include "wceq.mm"
include "cfv.mm"
include "sxsiga.mm"
include "cv.mm"
include "cmpt2.mm"
include "csigagen.mm"
include "eqid.mm"
include "sxval.mm"
include "unieqd.mm"
include "cvv.mm"
include "mpt2exga.mm"
include "rnexg.mm"
include "unisg.mm"
include "3syl.mm"
include "eqtrd.mm"
include "txuni2.mm"
include "syl6reqr.mm"
include "issgon.mm"
include "sylanbrc.mm"

theorem sxsigon
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) -> ( S sX T ) e. ( sigAlgebra ` ( U. S X. U. T ) ) )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    cT
    @0
    wcel
    wa
    #
    cS
    cT
    csx
    co
    #
    @0
    wcel
    cS
    cuni
    #
    cT
    cuni
    #
    cxp
    #
    @2
    cuni
    #
    wceq
    @2
    @5
    csiga
    cfv
    wcel
    cS
    cT
    sxsiga
    @1
    @6
    vx
    vy
    cS
    cT
    vx
    cv
    vy
    cv
    cxp
    #
    cmpt2
    #
    crn
    #
    cuni
    #
    @5
    @1
    @6
    @9
    csigagen
    cfv
    #
    cuni
    #
    @10
    @1
    @2
    @11
    vx
    vy
    @9
    cS
    cT
    @0
    @0
    @9
    eqid
    #
    sxval
    unieqd
    @1
    @8
    cvv
    wcel
    @9
    cvv
    wcel
    @12
    @10
    wceq
    vx
    vy
    cS
    cT
    @7
    @0
    @0
    mpt2exga
    @8
    cvv
    rnexg
    @9
    cvv
    unisg
    3syl
    eqtrd
    vx
    vy
    @9
    cS
    cT
    @3
    @4
    @13
    @3
    eqid
    @4
    eqid
    txuni2
    syl6reqr
    @2
    @5
    issgon
    sylanbrc
end
