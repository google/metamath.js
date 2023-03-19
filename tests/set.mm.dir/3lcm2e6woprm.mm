include "c3.mm"
include "c2.mm"
include "clcm.mm"
include "co.mm"
include "cmul.mm"
include "cgcd.mm"
include "cdiv.mm"
include "c1.mm"
include "c6.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "3cn.mm"
include "2cn.mm"
include "mulcli.mm"
include "cz.mm"
include "3z.mm"
include "2z.mm"
include "lcmcl.mm"
include "nn0cnd.mm"
include "mp2an.mm"
include "wn.mm"
include "pm3.2i.mm"
include "2ne0.mm"
include "neii.mm"
include "intnan.mm"
include "gcdn0cl.mm"
include "nncnd.mm"
include "cn.mm"
include "nnne0i.mm"
include "w3a.mm"
include "3nn.mm"
include "2nn.mm"
include "lcmgcdnn.mm"
include "eqcomd.mm"
include "mp1i.mm"
include "divmul3.mm"
include "mpbird.mm"
include "mp3an.mm"
include "gcdcom.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "1z.mm"
include "gcdid.mm"
include "ax-mp.mm"
include "abs1.mm"
include "eqtr2i.mm"
include "gcdadd.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "1p2e3.mm"
include "eqtri.mm"
include "3t2e6.mm"
include "oveq1i.mm"
include "6cn.mm"
include "div1i.mm"

theorem 3lcm2e6woprm



  assert |- ( 3 lcm 2 ) = 6

  proof
    c3
    c2
    clcm
    co
    #
    c3
    c2
    cmul
    co
    #
    c3
    c2
    cgcd
    co
    #
    cdiv
    co
    #
    @1
    c1
    cdiv
    co
    #
    c6
    @1
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    wa
    #
    @0
    @3
    wceq
    c3
    c2
    3cn
    2cn
    mulcli
    c3
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    @6
    3z
    2z
    @10
    @11
    wa
    #
    @0
    c3
    c2
    lcmcl
    nn0cnd
    mp2an
    @7
    @8
    @12
    c3
    cc0
    wceq
    #
    c2
    cc0
    wceq
    #
    wa
    wn
    #
    @7
    @10
    @11
    3z
    2z
    pm3.2i
    #
    @14
    @13
    c2
    cc0
    2ne0
    neii
    intnan
    #
    @12
    @15
    wa
    @2
    c3
    c2
    gcdn0cl
    #
    nncnd
    mp2an
    @2
    @12
    @15
    @2
    cn
    wcel
    @16
    @17
    @18
    mp2an
    nnne0i
    pm3.2i
    @5
    @6
    @9
    w3a
    #
    @3
    @0
    @19
    @3
    @0
    wceq
    @1
    @0
    @2
    cmul
    co
    #
    wceq
    #
    c3
    cn
    wcel
    #
    c2
    cn
    wcel
    #
    wa
    #
    @21
    @19
    @22
    @23
    3nn
    2nn
    pm3.2i
    @24
    @20
    @1
    c3
    c2
    lcmgcdnn
    eqcomd
    mp1i
    @1
    @0
    @2
    divmul3
    mpbird
    eqcomd
    mp3an
    @2
    c1
    @1
    cdiv
    @2
    c2
    c3
    cgcd
    co
    #
    c1
    @10
    @11
    @2
    @25
    wceq
    3z
    2z
    c3
    c2
    gcdcom
    mp2an
    c1
    c2
    c1
    c2
    caddc
    co
    #
    cgcd
    co
    #
    @25
    c1
    c1
    c2
    cgcd
    co
    #
    c2
    c1
    cgcd
    co
    #
    @27
    c1
    c1
    c1
    cgcd
    co
    #
    c1
    c1
    c1
    caddc
    co
    #
    cgcd
    co
    #
    @28
    @30
    c1
    cabs
    cfv
    #
    c1
    c1
    cz
    wcel
    #
    @30
    @33
    wceq
    1z
    c1
    gcdid
    ax-mp
    abs1
    eqtr2i
    @34
    @34
    @30
    @32
    wceq
    1z
    1z
    c1
    c1
    gcdadd
    mp2an
    @31
    c2
    c1
    cgcd
    1p1e2
    oveq2i
    3eqtri
    @34
    @11
    @28
    @29
    wceq
    1z
    2z
    c1
    c2
    gcdcom
    mp2an
    @11
    @34
    @29
    @27
    wceq
    2z
    1z
    c2
    c1
    gcdadd
    mp2an
    3eqtri
    @26
    c3
    c2
    cgcd
    1p2e3
    oveq2i
    eqtr2i
    eqtri
    oveq2i
    @4
    c6
    c1
    cdiv
    co
    c6
    @1
    c6
    c1
    cdiv
    3t2e6
    oveq1i
    c6
    6cn
    div1i
    eqtri
    3eqtri
end
