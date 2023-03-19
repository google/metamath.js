include "c4.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "c6.mm"
include "cc0.mm"
include "cfz.mm"
include "wcel.mm"
include "wceq.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "0z.mm"
include "4z.mm"
include "2z.mm"
include "3pm3.2i.mm"
include "0le2.mm"
include "2re.mm"
include "4re.mm"
include "2lt4.mm"
include "ltleii.mm"
include "pm3.2i.mm"
include "elfz4.mm"
include "mp2an.mm"
include "bcval2.mm"
include "ax-mp.mm"
include "c3.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "3nn0.mm"
include "facp1.mm"
include "df-4.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"
include "4cn.mm"
include "2cn.mm"
include "2p2e4.mm"
include "subaddrii.mm"
include "fac2.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "2t2e4.mm"
include "cn.mm"
include "faccl.mm"
include "nncni.mm"
include "4ne0.mm"
include "divcan4i.mm"
include "fac3.mm"

theorem 4bc2eq6



  assert |- ( 4 _C 2 ) = 6

  proof
    c4
    c2
    cbc
    co
    #
    c4
    cfa
    cfv
    #
    c4
    c2
    cmin
    co
    #
    cfa
    cfv
    #
    c2
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    c6
    c2
    cc0
    c4
    cfz
    co
    wcel
    #
    @0
    @6
    wceq
    cc0
    cz
    wcel
    #
    c4
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    w3a
    cc0
    c2
    cle
    wbr
    #
    c2
    c4
    cle
    wbr
    #
    wa
    @7
    @8
    @9
    @10
    0z
    4z
    2z
    3pm3.2i
    @11
    @12
    0le2
    c2
    c4
    2re
    4re
    2lt4
    ltleii
    pm3.2i
    c2
    cc0
    c4
    elfz4
    mp2an
    c2
    c4
    bcval2
    ax-mp
    @6
    c3
    cfa
    cfv
    #
    c4
    cmul
    co
    #
    c4
    cdiv
    co
    #
    c6
    @1
    @14
    @5
    c4
    cdiv
    c3
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @13
    @16
    cmul
    co
    #
    @1
    @14
    c3
    cn0
    wcel
    #
    @17
    @18
    wceq
    3nn0
    c3
    facp1
    ax-mp
    c4
    @16
    cfa
    df-4
    fveq2i
    c4
    @16
    @13
    cmul
    df-4
    oveq2i
    3eqtr4i
    @5
    c2
    c2
    cmul
    co
    c4
    @3
    c2
    @4
    c2
    cmul
    @3
    @4
    c2
    @2
    c2
    cfa
    c4
    c2
    c2
    4cn
    2cn
    2cn
    2p2e4
    subaddrii
    fveq2i
    fac2
    eqtri
    fac2
    oveq12i
    2t2e4
    eqtri
    oveq12i
    @15
    @13
    c6
    @13
    c4
    @13
    @19
    @13
    cn
    wcel
    3nn0
    c3
    faccl
    ax-mp
    nncni
    4cn
    4ne0
    divcan4i
    fac3
    eqtri
    eqtri
    eqtri
end
