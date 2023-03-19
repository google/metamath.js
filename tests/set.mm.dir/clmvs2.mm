include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "df-2.mm"
include "oveq1i.mm"
include "a1i.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl.mm"
include "cur.mm"
include "eqid.mm"
include "clm1.mm"
include "clmod.mm"
include "clmlmod.mm"
include "lmod1cl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "simpr.mm"
include "clmvsdir.mm"
include "syl13anc.mm"
include "clmvs1.mm"
include "oveq12d.mm"
include "3eqtrrd.mm"

theorem clmvs2
  let cA: class A
  let c.pl: class .+
  let c.x: class .x.
  let cV: class V
  let cW: class W
  assume clmvs1.v: |- V = ( Base ` W )
  assume clmvs1.s: |- .x. = ( .s ` W )
  assume clmvs2.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ A e. V ) -> ( A .+ A ) = ( 2 .x. A ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    c2
    cA
    c.x
    co
    #
    c1
    c1
    caddc
    co
    #
    cA
    c.x
    co
    #
    c1
    cA
    c.x
    co
    #
    @6
    c.pl
    co
    #
    cA
    cA
    c.pl
    co
    @3
    @5
    wceq
    @2
    c2
    @4
    cA
    c.x
    df-2
    oveq1i
    a1i
    @2
    @0
    c1
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @10
    @1
    @5
    @7
    wceq
    @0
    @1
    simpl
    @0
    @10
    @1
    @0
    c1
    @8
    cur
    cfv
    #
    @9
    @8
    cW
    @8
    eqid
    #
    clm1
    @0
    cW
    clmod
    wcel
    @11
    @9
    wcel
    cW
    clmlmod
    @11
    @8
    @9
    cW
    @12
    @9
    eqid
    #
    @11
    eqid
    lmod1cl
    syl
    eqeltrd
    adantr
    #
    @14
    @0
    @1
    simpr
    c.pl
    c1
    c1
    c.x
    @8
    @9
    cV
    cW
    cA
    clmvs1.v
    @12
    clmvs1.s
    @13
    clmvs2.a
    clmvsdir
    syl13anc
    @2
    @6
    cA
    @6
    cA
    c.pl
    c.x
    cV
    cW
    cA
    clmvs1.v
    clmvs1.s
    clmvs1
    #
    @15
    oveq12d
    3eqtrrd
end
