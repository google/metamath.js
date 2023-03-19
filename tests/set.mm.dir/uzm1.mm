include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wn.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "eluzel2.mm"
include "a1d.mm"
include "eluzelz.mm"
include "peano2zm.mm"
include "syl.mm"
include "clt.mm"
include "wne.mm"
include "df-ne.mm"
include "eluzle.mm"
include "wa.mm"
include "zred.mm"
include "eluzelre.mm"
include "ltlend.mm"
include "biimprd.mm"
include "mpand.mm"
include "syl5bir.mm"
include "wb.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "3jcad.mm"
include "eluz2.mm"
include "syl6ibr.mm"
include "orrd.mm"

theorem uzm1
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( N = M \/ ( N - 1 ) e. ( ZZ>= ` M ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cM
    wceq
    #
    cN
    c1
    cmin
    co
    #
    @0
    wcel
    #
    @1
    @2
    wn
    #
    cM
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    w3a
    @4
    @1
    @5
    @6
    @7
    @8
    @1
    @6
    @5
    cM
    cN
    eluzel2
    #
    a1d
    @1
    @7
    @5
    @1
    cN
    cz
    wcel
    #
    @7
    cM
    cN
    eluzelz
    #
    cN
    peano2zm
    syl
    a1d
    @1
    @5
    cM
    cN
    clt
    wbr
    #
    @8
    @5
    cN
    cM
    wne
    #
    @1
    @12
    cN
    cM
    df-ne
    @1
    cM
    cN
    cle
    wbr
    #
    @13
    @12
    cM
    cN
    eluzle
    @1
    @12
    @14
    @13
    wa
    @1
    cM
    cN
    @1
    cM
    @9
    zred
    cM
    cN
    eluzelre
    ltlend
    biimprd
    mpand
    syl5bir
    @1
    @6
    @10
    @12
    @8
    wb
    @9
    @11
    cM
    cN
    zltlem1
    syl2anc
    sylibd
    3jcad
    cM
    @3
    eluz2
    syl6ibr
    orrd
end
