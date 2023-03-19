include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cz.mm"
include "wi.mm"
include "nnz.mm"
include "dvdssqim.mm"
include "syl2an.mm"
include "cgcd.mm"
include "wceq.mm"
include "sqgcd.mm"
include "adantr.mm"
include "wb.mm"
include "nnsqcl.mm"
include "gcdeq.mm"
include "biimpar.mm"
include "eqtrd.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "nnre.mm"
include "nnnn0.mm"
include "sq11.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "gcddvds.mm"
include "simprd.mm"
include "eqbrtrrd.mm"
include "ex.mm"
include "impbid.mm"

theorem dvdssqlem
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( M || N <-> ( M ^ 2 ) || ( N ^ 2 ) ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cN
    cdvds
    wbr
    #
    cM
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    @0
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @3
    @6
    wi
    @1
    cM
    nnz
    #
    cN
    nnz
    #
    cM
    cN
    dvdssqim
    syl2an
    @2
    @6
    @3
    @2
    @6
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    cN
    cdvds
    @11
    @12
    c2
    cexp
    co
    #
    @4
    wceq
    #
    @12
    cM
    wceq
    #
    @11
    @13
    @4
    @5
    cgcd
    co
    #
    @4
    @2
    @13
    @16
    wceq
    @6
    cM
    cN
    sqgcd
    adantr
    @2
    @16
    @4
    wceq
    #
    @6
    @0
    @4
    cn
    wcel
    @5
    cn
    wcel
    @17
    @6
    wb
    @1
    cM
    nnsqcl
    cN
    nnsqcl
    @4
    @5
    gcdeq
    syl2an
    biimpar
    eqtrd
    @2
    @14
    @15
    wb
    #
    @6
    @2
    @12
    cr
    wcel
    cc0
    @12
    cle
    wbr
    cM
    cr
    wcel
    #
    cc0
    cM
    cle
    wbr
    #
    @18
    @2
    @12
    @0
    @7
    @8
    @12
    cn0
    wcel
    @1
    @9
    @10
    cM
    cN
    gcdcl
    syl2an
    #
    nn0red
    @2
    @12
    @21
    nn0ge0d
    @0
    @19
    @1
    cM
    nnre
    adantr
    @0
    @20
    @1
    @0
    cM
    cM
    nnnn0
    nn0ge0d
    adantr
    @12
    cM
    sq11
    syl22anc
    adantr
    mpbid
    @11
    @12
    cM
    cdvds
    wbr
    #
    @12
    cN
    cdvds
    wbr
    #
    @2
    @22
    @23
    wa
    #
    @6
    @0
    @7
    @8
    @24
    @1
    @9
    @10
    cM
    cN
    gcddvds
    syl2an
    adantr
    simprd
    eqbrtrrd
    ex
    impbid
end
