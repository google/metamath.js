include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "csrg.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "w3a.mm"
include "cop.mm"
include "pm4.24.mm"
include "cmgm.mm"
include "wb.mm"
include "cmnd.mm"
include "srgmnd.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "mndmgm.mm"
include "syl.mm"
include "simpr.mm"
include "simpl2.mm"
include "mgmb1mgm1.mm"
include "syl3anc.mm"
include "cmgp.mm"
include "cfv.mm"
include "cplusg.mm"
include "simpl1.mm"
include "eqid.mm"
include "srgmgp.mm"
include "3syl.mm"
include "mgpplusg.mm"
include "fneq1i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "mgpbas.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "syl5bb.mm"

theorem srg1zr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cZ: class Z
  assume srg1zr.b: |- B = ( Base ` R )
  assume srg1zr.p: |- .+ = ( +g ` R )
  assume srg1zr.t: |- .* = ( .r ` R )


  assert |- ( ( ( R e. SRing /\ .+ Fn ( B X. B ) /\ .* Fn ( B X. B ) ) /\ Z e. B ) -> ( B = { Z } <-> ( .+ = { <. <. Z , Z >. , Z >. } /\ .* = { <. <. Z , Z >. , Z >. } ) ) )

  proof
    cB
    cZ
    csn
    wceq
    #
    @0
    @0
    wa
    cR
    csrg
    wcel
    #
    c.pl
    cB
    cB
    cxp
    #
    wfn
    #
    c.as
    @2
    wfn
    #
    w3a
    #
    cZ
    cB
    wcel
    #
    wa
    #
    c.pl
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    wceq
    #
    c.as
    @8
    wceq
    #
    wa
    @0
    pm4.24
    @7
    @0
    @9
    @0
    @10
    @7
    cR
    cmgm
    wcel
    #
    @6
    @3
    @0
    @9
    wb
    @7
    cR
    cmnd
    wcel
    #
    @11
    @5
    @12
    @6
    @1
    @3
    @12
    @4
    cR
    srgmnd
    3ad2ant1
    adantr
    cR
    mndmgm
    syl
    @5
    @6
    simpr
    #
    @1
    @3
    @4
    @6
    simpl2
    cB
    c.pl
    cR
    cZ
    srg1zr.b
    srg1zr.p
    mgmb1mgm1
    syl3anc
    @7
    @0
    cR
    cmgp
    cfv
    #
    cplusg
    cfv
    #
    @8
    wceq
    #
    @10
    @7
    @14
    cmgm
    wcel
    #
    @6
    @15
    @2
    wfn
    #
    @0
    @16
    wb
    @7
    @1
    @14
    cmnd
    wcel
    @17
    @1
    @3
    @4
    @6
    simpl1
    cR
    @14
    @14
    eqid
    #
    srgmgp
    @14
    mndmgm
    3syl
    @13
    @5
    @18
    @6
    @4
    @1
    @18
    @3
    @4
    @18
    @2
    c.as
    @15
    cR
    c.as
    @14
    @19
    srg1zr.t
    mgpplusg
    #
    fneq1i
    biimpi
    3ad2ant3
    adantr
    cB
    @15
    @14
    cZ
    cB
    cR
    @14
    @19
    srg1zr.b
    mgpbas
    @15
    eqid
    mgmb1mgm1
    syl3anc
    @7
    @15
    c.as
    @8
    @15
    c.as
    wceq
    @7
    c.as
    @15
    @20
    eqcomi
    a1i
    eqeq1d
    bitrd
    anbi12d
    syl5bb
end
