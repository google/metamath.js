include "cmgm.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "w3a.mm"
include "wf.mm"
include "csn.mm"
include "wceq.mm"
include "cop.mm"
include "wb.mm"
include "cplusf.mm"
include "cfv.mm"
include "wi.mm"
include "eqid.mm"
include "plusfeq.mm"
include "mgmplusf.mm"
include "feq1.mm"
include "syl5ib.mm"
include "syl.mm"
include "impcom.mm"
include "3adant2.mm"
include "simp2.mm"
include "intopsn.mm"
include "syl2anc.mm"

theorem mgmb1mgm1
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cZ: class Z
  assume mgmb1mgm1.b: |- B = ( Base ` M )
  assume mgmb1mgm1.p: |- .+ = ( +g ` M )


  assert |- ( ( M e. Mgm /\ Z e. B /\ .+ Fn ( B X. B ) ) -> ( B = { Z } <-> .+ = { <. <. Z , Z >. , Z >. } ) )

  proof
    cM
    cmgm
    wcel
    #
    cZ
    cB
    wcel
    #
    c.pl
    cB
    cB
    cxp
    #
    wfn
    #
    w3a
    @2
    cB
    c.pl
    wf
    #
    @1
    cB
    cZ
    csn
    wceq
    c.pl
    cZ
    cZ
    cop
    cZ
    cop
    csn
    wceq
    wb
    @0
    @3
    @4
    @1
    @3
    @0
    @4
    @3
    cM
    cplusf
    cfv
    #
    c.pl
    wceq
    #
    @0
    @4
    wi
    cB
    c.pl
    @5
    cM
    mgmb1mgm1.b
    mgmb1mgm1.p
    @5
    eqid
    #
    plusfeq
    @0
    @2
    cB
    @5
    wf
    @6
    @4
    cB
    @5
    cM
    mgmb1mgm1.b
    @7
    mgmplusf
    @2
    cB
    @5
    c.pl
    feq1
    syl5ib
    syl
    impcom
    3adant2
    @0
    @1
    @3
    simp2
    cB
    c.pl
    cZ
    intopsn
    syl2anc
end
