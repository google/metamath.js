include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "codd.mm"
include "eldifsn.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "prmz.mm"
include "adantr.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "necom.mm"
include "df-ne.mm"
include "sylbb.mm"
include "adantl.mm"
include "1ne2.mm"
include "nesymi.mm"
include "a1i.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "dvdsprime.mm"
include "sylan2.mm"
include "mtbird.mm"
include "isodd3.mm"
include "sylbi.mm"

theorem oddprmALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ( Prime \ { 2 } ) -> N e. Odd )

  proof
    cN
    cprime
    c2
    csn
    cdif
    wcel
    cN
    cprime
    wcel
    #
    cN
    c2
    wne
    #
    wa
    #
    cN
    codd
    wcel
    #
    cN
    cprime
    c2
    eldifsn
    @2
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    @3
    @0
    @4
    @1
    cN
    prmz
    adantr
    @2
    @5
    c2
    cN
    wceq
    #
    c2
    c1
    wceq
    #
    wo
    #
    @2
    @6
    wn
    #
    @7
    wn
    #
    @8
    wn
    @1
    @9
    @0
    @1
    c2
    cN
    wne
    @9
    cN
    c2
    necom
    c2
    cN
    df-ne
    sylbb
    adantl
    @10
    @2
    c1
    c2
    1ne2
    nesymi
    a1i
    @6
    @7
    ioran
    sylanbrc
    @1
    @0
    c2
    cn
    wcel
    #
    @5
    @8
    wb
    @11
    @1
    2nn
    a1i
    cN
    c2
    dvdsprime
    sylan2
    mtbird
    cN
    isodd3
    sylanbrc
    sylbi
end
