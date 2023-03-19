include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgrp.mm"
include "simpl1.mm"
include "ablgrp.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "odcl.mm"
include "nn0mulcld.mm"
include "simpr.mm"
include "oveq2d.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "odadd1.mm"
include "adantr.mm"
include "eqbrtrrd.mm"
include "c2.mm"
include "cexp.mm"
include "odadd2.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "dvdseq.mm"
include "syl22anc.mm"

theorem odadd
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cO: class O
  let cX: class X
  assume odadd1.1: |- O = ( od ` G )
  assume odadd1.2: |- X = ( Base ` G )
  assume odadd1.3: |- .+ = ( +g ` G )


  assert |- ( ( ( G e. Abel /\ A e. X /\ B e. X ) /\ ( ( O ` A ) gcd ( O ` B ) ) = 1 ) -> ( O ` ( A .+ B ) ) = ( ( O ` A ) x. ( O ` B ) ) )

  proof
    cG
    cabl
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cB
    cO
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    cA
    cB
    c.pl
    co
    #
    cO
    cfv
    #
    cn0
    wcel
    #
    @4
    @5
    cmul
    co
    #
    cn0
    wcel
    @10
    @12
    cdvds
    wbr
    @12
    @10
    cdvds
    wbr
    @10
    @12
    wceq
    @8
    @9
    cX
    wcel
    #
    @11
    @8
    cG
    cgrp
    wcel
    #
    @1
    @2
    @13
    @8
    @0
    @14
    @0
    @1
    @2
    @7
    simpl1
    cG
    ablgrp
    syl
    @0
    @1
    @2
    @7
    simpl2
    #
    @0
    @1
    @2
    @7
    simpl3
    #
    cX
    c.pl
    cG
    cA
    cB
    odadd1.2
    odadd1.3
    grpcl
    syl3anc
    @9
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    syl
    #
    @8
    @4
    @5
    @8
    @1
    @4
    cn0
    wcel
    @15
    cA
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    syl
    @8
    @2
    @5
    cn0
    wcel
    @16
    cB
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    syl
    nn0mulcld
    @8
    @10
    @6
    cmul
    co
    #
    @10
    @12
    cdvds
    @8
    @18
    @10
    c1
    cmul
    co
    #
    @10
    @8
    @6
    c1
    @10
    cmul
    @3
    @7
    simpr
    #
    oveq2d
    @8
    @10
    @8
    @10
    @17
    nn0cnd
    mulid1d
    #
    eqtrd
    @3
    @18
    @12
    cdvds
    wbr
    @7
    cA
    cB
    c.pl
    cG
    cO
    cX
    odadd1.1
    odadd1.2
    odadd1.3
    odadd1
    adantr
    eqbrtrrd
    @8
    @12
    @10
    @6
    c2
    cexp
    co
    #
    cmul
    co
    #
    @10
    cdvds
    @3
    @12
    @23
    cdvds
    wbr
    @7
    cA
    cB
    c.pl
    cG
    cO
    cX
    odadd1.1
    odadd1.2
    odadd1.3
    odadd2
    adantr
    @8
    @23
    @19
    @10
    @8
    @22
    c1
    @10
    cmul
    @8
    @22
    c1
    c2
    cexp
    co
    c1
    @8
    @6
    c1
    c2
    cexp
    @20
    oveq1d
    sq1
    syl6eq
    oveq2d
    @21
    eqtrd
    breqtrd
    @10
    @12
    dvdseq
    syl22anc
end
