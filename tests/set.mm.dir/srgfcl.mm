include "csrg.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "simpr.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "co.mm"
include "srgcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "syl6bb.mm"
include "ralxp.mm"
include "sylibr.mm"
include "adantr.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem srgfcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume srgfcl.b: |- B = ( Base ` R )
  assume srgfcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. SRing /\ .x. Fn ( B X. B ) ) -> .x. : ( B X. B ) --> B )

  proof
    cR
    csrg
    wcel
    #
    c.x
    cB
    cB
    cxp
    #
    wfn
    #
    wa
    #
    @2
    c.x
    crn
    cB
    wss
    #
    @1
    cB
    c.x
    wf
    @0
    @2
    simpr
    #
    @3
    @2
    vc
    cv
    #
    c.x
    cfv
    #
    cB
    wcel
    #
    vc
    @1
    wral
    #
    @4
    @5
    @0
    @9
    @2
    @0
    va
    cv
    #
    vb
    cv
    #
    c.x
    co
    #
    cB
    wcel
    #
    vb
    cB
    wral
    va
    cB
    wral
    @9
    @0
    @13
    va
    vb
    cB
    cB
    @0
    @10
    cB
    wcel
    @11
    cB
    wcel
    @13
    cB
    cR
    c.x
    @10
    @11
    srgfcl.b
    srgfcl.t
    srgcl
    3expb
    ralrimivva
    @8
    @13
    vc
    va
    vb
    cB
    cB
    @6
    @10
    @11
    cop
    #
    wceq
    #
    @8
    @14
    c.x
    cfv
    #
    cB
    wcel
    @13
    @15
    @7
    @16
    cB
    @6
    @14
    c.x
    fveq2
    eleq1d
    @16
    @12
    cB
    @12
    @16
    @10
    @11
    c.x
    df-ov
    eqcomi
    eleq1i
    syl6bb
    ralxp
    sylibr
    adantr
    vc
    @1
    cB
    c.x
    fnfvrnss
    syl2anc
    @1
    cB
    c.x
    df-f
    sylanbrc
end
