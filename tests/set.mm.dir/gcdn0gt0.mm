include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cn0.mm"
include "wb.mm"
include "gcdcl.mm"
include "cr.mm"
include "cle.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "0re.mm"
include "leltne.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "syl.mm"
include "gcdeq0.mm"
include "necon3abid.mm"
include "bitr2d.mm"

theorem gcdn0gt0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( -. ( M = 0 /\ N = 0 ) <-> 0 < ( M gcd N ) ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cc0
    cM
    cN
    cgcd
    co
    #
    clt
    wbr
    #
    @1
    cc0
    wne
    #
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    #
    wn
    @0
    @1
    cn0
    wcel
    #
    @2
    @3
    wb
    #
    cM
    cN
    gcdcl
    @5
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @6
    @1
    nn0re
    @1
    nn0ge0
    cc0
    cr
    wcel
    @7
    @8
    @6
    0re
    cc0
    @1
    leltne
    mp3an1
    syl2anc
    syl
    @0
    @4
    @1
    cc0
    cM
    cN
    gcdeq0
    necon3abid
    bitr2d
end
