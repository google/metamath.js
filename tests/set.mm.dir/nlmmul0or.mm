include "cnlm.mm"
include "wcel.mm"
include "w3a.mm"
include "cnm.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cngp.mm"
include "cr.mm"
include "nlmngp2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqid.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "nlmngp.mm"
include "simp3.mm"
include "mul0ord.mm"
include "nmvs.mm"
include "eqeq1d.mm"
include "wb.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodvscl.mm"
include "syl3an1.mm"
include "nmeq0.mm"
include "bitr3d.mm"
include "orbi12d.mm"
include "3bitr3d.mm"

theorem nlmmul0or
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume nlmmul0or.v: |- V = ( Base ` W )
  assume nlmmul0or.s: |- .x. = ( .s ` W )
  assume nlmmul0or.z: |- .0. = ( 0g ` W )
  assume nlmmul0or.f: |- F = ( Scalar ` W )
  assume nlmmul0or.k: |- K = ( Base ` F )
  assume nlmmul0or.o: |- O = ( 0g ` F )


  assert |- ( ( W e. NrmMod /\ A e. K /\ B e. V ) -> ( ( A .x. B ) = .0. <-> ( A = O \/ B = .0. ) ) )

  proof
    cW
    cnlm
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cF
    cnm
    cfv
    #
    cfv
    #
    cB
    cW
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cc0
    wceq
    #
    @5
    cc0
    wceq
    #
    @7
    cc0
    wceq
    #
    wo
    cA
    cB
    c.x
    co
    #
    c.0
    wceq
    #
    cA
    cO
    wceq
    #
    cB
    c.0
    wceq
    #
    wo
    @3
    @5
    @7
    @3
    @5
    @3
    cF
    cngp
    wcel
    #
    @1
    @5
    cr
    wcel
    @0
    @1
    @16
    @2
    cF
    cW
    nlmmul0or.f
    nlmngp2
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    cA
    cF
    @4
    cK
    nlmmul0or.k
    @4
    eqid
    #
    nmcl
    syl2anc
    recnd
    @3
    @7
    @3
    cW
    cngp
    wcel
    #
    @2
    @7
    cr
    wcel
    @0
    @1
    @20
    @2
    cW
    nlmngp
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cW
    @6
    cV
    nlmmul0or.v
    @6
    eqid
    #
    nmcl
    syl2anc
    recnd
    mul0ord
    @3
    @12
    @6
    cfv
    #
    cc0
    wceq
    #
    @9
    @13
    @3
    @24
    @8
    cc0
    @4
    c.x
    cF
    cK
    @6
    cV
    cW
    cA
    cB
    nlmmul0or.v
    @23
    nlmmul0or.s
    nlmmul0or.f
    nlmmul0or.k
    @19
    nmvs
    eqeq1d
    @3
    @20
    @12
    cV
    wcel
    #
    @25
    @13
    wb
    @21
    @0
    cW
    clmod
    wcel
    @1
    @2
    @26
    cW
    nlmlmod
    cA
    c.x
    cF
    cK
    cV
    cW
    cB
    nlmmul0or.v
    nlmmul0or.f
    nlmmul0or.s
    nlmmul0or.k
    lmodvscl
    syl3an1
    @12
    cW
    @6
    cV
    c.0
    nlmmul0or.v
    @23
    nlmmul0or.z
    nmeq0
    syl2anc
    bitr3d
    @3
    @10
    @14
    @11
    @15
    @3
    @16
    @1
    @10
    @14
    wb
    @17
    @18
    cA
    cF
    @4
    cK
    cO
    nlmmul0or.k
    @19
    nlmmul0or.o
    nmeq0
    syl2anc
    @3
    @20
    @2
    @11
    @15
    wb
    @21
    @22
    cB
    cW
    @6
    cV
    c.0
    nlmmul0or.v
    @23
    nlmmul0or.z
    nmeq0
    syl2anc
    orbi12d
    3bitr3d
end
