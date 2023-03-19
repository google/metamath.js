include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "cc0.mm"
include "wb.mm"
include "zre.mm"
include "readdcl.mm"
include "sylan.mm"
include "simpl.mm"
include "flbi.mm"
include "syl2anc.mm"
include "addge01.mm"
include "1re.mm"
include "ltadd2.mm"
include "mp3an2.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "bitr4d.mm"

theorem flbi2
  let cF: class F
  let cN: class N


  assert |- ( ( N e. ZZ /\ F e. RR ) -> ( ( |_ ` ( N + F ) ) = N <-> ( 0 <_ F /\ F < 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    cF
    cr
    wcel
    #
    wa
    #
    cN
    cF
    caddc
    co
    #
    cfl
    cfv
    cN
    wceq
    #
    cN
    @3
    cle
    wbr
    #
    @3
    cN
    c1
    caddc
    co
    clt
    wbr
    #
    wa
    #
    cc0
    cF
    cle
    wbr
    #
    cF
    c1
    clt
    wbr
    #
    wa
    #
    @2
    @3
    cr
    wcel
    #
    @0
    @4
    @7
    wb
    @0
    cN
    cr
    wcel
    #
    @1
    @11
    cN
    zre
    #
    cN
    cF
    readdcl
    sylan
    @0
    @1
    simpl
    @3
    cN
    flbi
    syl2anc
    @0
    @12
    @1
    @10
    @7
    wb
    @13
    @12
    @1
    wa
    @8
    @5
    @9
    @6
    cN
    cF
    addge01
    @1
    @12
    @9
    @6
    wb
    #
    @1
    c1
    cr
    wcel
    @12
    @14
    1re
    cF
    c1
    cN
    ltadd2
    mp3an2
    ancoms
    anbi12d
    sylan
    bitr4d
end
