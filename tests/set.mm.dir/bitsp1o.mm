include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cbits.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "wb.mm"
include "2z.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "peano2zd.mm"
include "bitsp1.mm"
include "sylan.mm"
include "wceq.mm"
include "cr.mm"
include "2re.mm"
include "zre.mm"
include "remulcld.mm"
include "recnd.mm"
include "1cnd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divdird.mm"
include "zcn.mm"
include "divcan3d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "0re.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "halflt1.mm"
include "pm3.2i.mm"
include "flbi2.mm"
include "mpan2.mm"
include "mpbiri.mm"
include "adantr.mm"
include "eleq2d.mm"
include "bitrd.mm"

theorem bitsp1o
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( ( M + 1 ) e. ( bits ` ( ( 2 x. N ) + 1 ) ) <-> M e. ( bits ` N ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cM
    c1
    caddc
    co
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cbits
    cfv
    wcel
    #
    cM
    @4
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cbits
    cfv
    #
    wcel
    #
    cM
    cN
    cbits
    cfv
    #
    wcel
    @0
    @4
    cz
    wcel
    @1
    @5
    @9
    wb
    @0
    @3
    @0
    c2
    cN
    c2
    cz
    wcel
    @0
    2z
    a1i
    @0
    id
    zmulcld
    peano2zd
    cM
    @4
    bitsp1
    sylan
    @2
    @8
    @10
    cM
    @2
    @7
    cN
    cbits
    @0
    @7
    cN
    wceq
    @1
    @0
    @7
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cN
    @0
    @6
    @12
    cfl
    @0
    @6
    @3
    c2
    cdiv
    co
    #
    @11
    caddc
    co
    @12
    @0
    @3
    c1
    c2
    @0
    @3
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    cN
    zre
    remulcld
    recnd
    @0
    1cnd
    @0
    2cnd
    #
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    divdird
    @0
    @14
    cN
    @11
    caddc
    @0
    cN
    c2
    cN
    zcn
    @15
    @16
    divcan3d
    oveq1d
    eqtrd
    fveq2d
    @0
    @13
    cN
    wceq
    #
    cc0
    @11
    cle
    wbr
    #
    @11
    c1
    clt
    wbr
    #
    wa
    #
    @18
    @19
    cc0
    @11
    0re
    halfre
    halfgt0
    ltleii
    halflt1
    pm3.2i
    @0
    @11
    cr
    wcel
    @17
    @20
    wb
    halfre
    @11
    cN
    flbi2
    mpan2
    mpbiri
    eqtrd
    adantr
    fveq2d
    eleq2d
    bitrd
end
