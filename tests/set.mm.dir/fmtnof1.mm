include "cn0.mm"
include "cn.mm"
include "cfmtno.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "df-fmtno.mm"
include "wcel.mm"
include "2nn.mm"
include "a1i.mm"
include "2nn0.mm"
include "id.mm"
include "nn0expcld.mm"
include "nnexpcld.mm"
include "peano2nnd.mm"
include "fmpti.mm"
include "wa.mm"
include "fmtno.mm"
include "eqeqan12d.mm"
include "cc.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "adantl.mm"
include "1cnd.mm"
include "addcan2d.mm"
include "cr.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "2re.mm"
include "nn0zd.mm"
include "1lt2.mm"
include "expcan.mm"
include "syl31anc.mm"
include "bitrd.mm"
include "nn0z.mm"
include "w3a.mm"
include "biimpd.mm"
include "sylbid.mm"
include "rgen2.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem fmtnof1
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- FermatNo : NN0 -1-1-> NN

  proof
    cn0
    cn
    cfmtno
    wf1
    cn0
    cn
    cfmtno
    wf
    vn
    cv
    #
    cfmtno
    cfv
    #
    vm
    cv
    #
    cfmtno
    cfv
    #
    wceq
    #
    vn
    vm
    weq
    #
    wi
    #
    vm
    cn0
    wral
    vn
    cn0
    wral
    vn
    cn0
    cn
    c2
    c2
    @0
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cfmtno
    vn
    df-fmtno
    @0
    cn0
    wcel
    #
    @8
    @10
    c2
    @7
    c2
    cn
    wcel
    @10
    2nn
    a1i
    @10
    c2
    @0
    c2
    cn0
    wcel
    #
    @10
    2nn0
    a1i
    #
    @10
    id
    nn0expcld
    #
    nnexpcld
    peano2nnd
    fmpti
    @6
    vn
    vm
    cn0
    cn0
    @10
    @2
    cn0
    wcel
    #
    wa
    #
    @4
    @9
    c2
    c2
    @2
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    @5
    @10
    @14
    @1
    @9
    @3
    @18
    @0
    fmtno
    @2
    fmtno
    eqeqan12d
    @15
    @19
    @7
    @16
    wceq
    #
    @5
    @15
    @19
    @8
    @17
    wceq
    #
    @20
    @15
    @8
    @17
    c1
    @10
    @8
    cc
    wcel
    @14
    @10
    @8
    @10
    c2
    @7
    @12
    @13
    nn0expcld
    nn0cnd
    adantr
    @14
    @17
    cc
    wcel
    @10
    @14
    @17
    @14
    c2
    @16
    @11
    @14
    2nn0
    a1i
    #
    @14
    c2
    @2
    @22
    @14
    id
    nn0expcld
    #
    nn0expcld
    nn0cnd
    adantl
    @15
    1cnd
    addcan2d
    @15
    c2
    cr
    wcel
    #
    @7
    cz
    wcel
    #
    @16
    cz
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @21
    @20
    wb
    @24
    @15
    2re
    a1i
    #
    @10
    @25
    @14
    @10
    @7
    @13
    nn0zd
    adantr
    @14
    @26
    @10
    @14
    @16
    @23
    nn0zd
    adantl
    @27
    @15
    1lt2
    a1i
    #
    c2
    @7
    @16
    expcan
    syl31anc
    bitrd
    @15
    @24
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @27
    @20
    @5
    wi
    @28
    @10
    @30
    @14
    @0
    nn0z
    adantr
    @14
    @31
    @10
    @2
    nn0z
    adantl
    @29
    @24
    @30
    @31
    w3a
    @27
    wa
    @20
    @5
    c2
    @0
    @2
    expcan
    biimpd
    syl31anc
    sylbid
    sylbid
    rgen2
    vn
    vm
    cn0
    cn
    cfmtno
    dff13
    mpbir2an
end
