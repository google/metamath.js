include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "nnre.mm"
include "orc.mm"
include "nngt0.mm"
include "jca31.mm"
include "wi.mm"
include "idd.mm"
include "wn.mm"
include "lt0neg2.mm"
include "renegcl.mm"
include "0re.mm"
include "ltnsym.mm"
include "sylancl.mm"
include "sylbid.mm"
include "imp.mm"
include "nsyl.mm"
include "gt0ne0.mm"
include "neneqd.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "pm2.21d.mm"
include "jaod.mm"
include "ex.mm"
include "com23.mm"
include "imp31.mm"
include "impbii.mm"
include "w3o.mm"
include "elz.mm"
include "3orrot.mm"
include "3orass.mm"
include "bitri.mm"
include "anbi2i.mm"
include "anbi1i.mm"
include "bitr4i.mm"

theorem elnnz
  let cN: class N


  assert |- ( N e. NN <-> ( N e. ZZ /\ 0 < N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cr
    wcel
    #
    @0
    cN
    cneg
    #
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    #
    wo
    #
    wa
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    cN
    cz
    wcel
    #
    @8
    wa
    @0
    @9
    @0
    @1
    @6
    @8
    cN
    nnre
    @0
    @5
    orc
    cN
    nngt0
    jca31
    @1
    @6
    @8
    @0
    @1
    @8
    @6
    @0
    @1
    @8
    @6
    @0
    wi
    @1
    @8
    wa
    #
    @0
    @0
    @5
    @11
    @0
    idd
    @11
    @5
    @0
    @11
    @3
    wn
    @4
    wn
    @5
    wn
    @11
    cc0
    @2
    clt
    wbr
    #
    @3
    @1
    @8
    @12
    wn
    #
    @1
    @8
    @2
    cc0
    clt
    wbr
    #
    @13
    cN
    lt0neg2
    @1
    @2
    cr
    wcel
    cc0
    cr
    wcel
    @14
    @13
    wi
    cN
    renegcl
    0re
    @2
    cc0
    ltnsym
    sylancl
    sylbid
    imp
    @2
    nngt0
    nsyl
    @11
    cN
    cc0
    cN
    gt0ne0
    neneqd
    @3
    @4
    ioran
    sylanbrc
    pm2.21d
    jaod
    ex
    com23
    imp31
    impbii
    @10
    @7
    @8
    @10
    @1
    @4
    @0
    @3
    w3o
    #
    wa
    @7
    cN
    elz
    @15
    @6
    @1
    @15
    @0
    @3
    @4
    w3o
    @6
    @4
    @0
    @3
    3orrot
    @0
    @3
    @4
    3orass
    bitri
    anbi2i
    bitri
    anbi1i
    bitr4i
end
