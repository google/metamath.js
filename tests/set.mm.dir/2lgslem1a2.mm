include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "c4.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "zre.mm"
include "rehalfcld.mm"
include "adantr.mm"
include "id.mm"
include "2z.mm"
include "a1i.mm"
include "zmulcld.mm"
include "zred.mm"
include "adantl.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltdiv1.mm"
include "syl3anc.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "zcn.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "2t2e4.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan4d.mm"
include "breq12d.mm"
include "4re.mm"
include "4ne0.mm"
include "redivcld.mm"
include "fllt.mm"
include "sylan.mm"
include "3bitrrd.mm"

theorem 2lgslem1a2
  let cI: class I
  let cN: class N


  assert |- ( ( N e. ZZ /\ I e. ZZ ) -> ( ( |_ ` ( N / 4 ) ) < I <-> ( N / 2 ) < ( I x. 2 ) ) )

  proof
    cN
    cz
    wcel
    #
    cI
    cz
    wcel
    #
    wa
    #
    cN
    c2
    cdiv
    co
    #
    cI
    c2
    cmul
    co
    #
    clt
    wbr
    #
    @3
    c2
    cdiv
    co
    #
    @4
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cN
    c4
    cdiv
    co
    #
    cI
    clt
    wbr
    #
    @9
    cfl
    cfv
    cI
    clt
    wbr
    #
    @2
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @5
    @8
    wb
    @0
    @12
    @1
    @0
    cN
    cN
    zre
    #
    rehalfcld
    adantr
    @1
    @13
    @0
    @1
    @4
    @1
    cI
    c2
    @1
    id
    c2
    cz
    wcel
    @1
    2z
    a1i
    zmulcld
    zred
    adantl
    @16
    @2
    @14
    @15
    2re
    2pos
    pm3.2i
    a1i
    @3
    @4
    c2
    ltdiv1
    syl3anc
    @2
    @6
    @9
    @7
    cI
    clt
    @2
    @6
    cN
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @9
    @2
    cN
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @22
    @6
    @19
    wceq
    @0
    @20
    @1
    cN
    zcn
    adantr
    @22
    @2
    2cnne0
    a1i
    #
    @23
    cN
    c2
    c2
    divdiv1
    syl3anc
    @18
    c4
    cN
    cdiv
    2t2e4
    oveq2i
    syl6eq
    @2
    cI
    c2
    @1
    cI
    cc
    wcel
    @0
    cI
    zcn
    adantl
    @2
    2cnd
    @21
    @2
    2ne0
    a1i
    divcan4d
    breq12d
    @0
    @9
    cr
    wcel
    @1
    @10
    @11
    wb
    @0
    cN
    c4
    @17
    c4
    cr
    wcel
    @0
    4re
    a1i
    c4
    cc0
    wne
    @0
    4ne0
    a1i
    redivcld
    @9
    cI
    fllt
    sylan
    3bitrrd
end
