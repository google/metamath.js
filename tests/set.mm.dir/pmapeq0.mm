include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "cal.mm"
include "hlatl.mm"
include "adantr.mm"
include "pmap0.mm"
include "syl.mm"
include "eqeq2d.mm"
include "wb.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "pmap11.mm"
include "mpd3an3.mm"
include "bitr3d.mm"

theorem pmapeq0
  let cB: class B
  let cK: class K
  let cM: class M
  let cX: class X
  let c.0: class .0.
  assume pmapeq0.b: |- B = ( Base ` K )
  assume pmapeq0.z: |- .0. = ( 0. ` K )
  assume pmapeq0.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( ( M ` X ) = (/) <-> X = .0. ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cM
    cfv
    #
    c.0
    cM
    cfv
    #
    wceq
    #
    @3
    c0
    wceq
    cX
    c.0
    wceq
    #
    @2
    @4
    c0
    @3
    @2
    cK
    cal
    wcel
    #
    @4
    c0
    wceq
    @0
    @7
    @1
    cK
    hlatl
    adantr
    cK
    cM
    c.0
    pmapeq0.z
    pmapeq0.m
    pmap0
    syl
    eqeq2d
    @0
    @1
    c.0
    cB
    wcel
    #
    @5
    @6
    wb
    @2
    cK
    cops
    wcel
    #
    @8
    @0
    @9
    @1
    cK
    hlop
    adantr
    cB
    cK
    c.0
    pmapeq0.b
    pmapeq0.z
    op0cl
    syl
    cB
    cK
    cM
    cX
    c.0
    pmapeq0.b
    pmapeq0.m
    pmap11
    mpd3an3
    bitr3d
end
