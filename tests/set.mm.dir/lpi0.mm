include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "cv.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "eqid.mm"
include "ring0cl.mm"
include "rsp0.mm"
include "eqcomd.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "islpidl.mm"
include "mpbird.mm"

theorem lpi0
  let cP: class P
  let cR: class R
  let c.0: class .0.
  let vr: setvar r
  let vg: setvar g
  let cB: class B
  let cK: class K
  let cU: class U
  let cI: class I
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpi0.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> { .0. } e. P )

  proof
    cR
    crg
    wcel
    #
    c.0
    csn
    #
    cP
    wcel
    @1
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
    cR
    cbs
    cfv
    #
    wrex
    #
    @0
    c.0
    @7
    wcel
    @1
    @1
    @4
    cfv
    #
    wceq
    #
    @8
    @7
    cR
    c.0
    @7
    eqid
    #
    lpi0.z
    ring0cl
    @0
    @9
    @1
    cR
    @4
    c.0
    @4
    eqid
    #
    lpi0.z
    rsp0
    eqcomd
    @6
    @10
    vg
    c.0
    @7
    @2
    c.0
    wceq
    #
    @5
    @9
    @1
    @13
    @3
    @1
    @4
    @2
    c.0
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    @7
    cP
    cR
    vg
    @1
    @4
    lpival.p
    @12
    @11
    islpidl
    mpbird
end
