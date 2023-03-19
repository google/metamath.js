include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cur.mm"
include "eqid.mm"
include "ringidcl.mm"
include "rsp1.mm"
include "eqcomd.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "islpidl.mm"
include "mpbird.mm"

theorem lpi1
  let cB: class B
  let cP: class P
  let cR: class R
  let vr: setvar r
  let vg: setvar g
  let cK: class K
  let cU: class U
  let cI: class I
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpi1.b: |- B = ( Base ` R )


  assert |- ( R e. Ring -> B e. P )

  proof
    cR
    crg
    wcel
    #
    cB
    cP
    wcel
    cB
    vg
    cv
    #
    csn
    #
    cR
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vg
    cB
    wrex
    #
    @0
    cR
    cur
    cfv
    #
    cB
    wcel
    cB
    @7
    csn
    #
    @3
    cfv
    #
    wceq
    #
    @6
    cB
    cR
    @7
    lpi1.b
    @7
    eqid
    #
    ringidcl
    @0
    @9
    cB
    cB
    cR
    @7
    @3
    @3
    eqid
    #
    lpi1.b
    @11
    rsp1
    eqcomd
    @5
    @10
    vg
    @7
    cB
    @1
    @7
    wceq
    #
    @4
    @9
    cB
    @13
    @2
    @8
    @3
    @1
    @7
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    cB
    cP
    cR
    vg
    cB
    @3
    lpival.p
    @12
    lpi1.b
    islpidl
    mpbird
end
