include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzel2.mm"
include "adantl.mm"
include "eluzelz.mm"
include "adantr.mm"
include "eluzle.mm"
include "wi.mm"
include "zletr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "eluz2.mm"
include "syl3anbrc.mm"

theorem uztrn
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ( ZZ>= ` K ) /\ K e. ( ZZ>= ` N ) ) -> M e. ( ZZ>= ` N ) )

  proof
    cM
    cK
    cuz
    cfv
    wcel
    #
    cK
    cN
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cM
    cle
    wbr
    #
    cM
    @1
    wcel
    @2
    @4
    @0
    cN
    cK
    eluzel2
    adantl
    #
    @0
    @5
    @2
    cK
    cM
    eluzelz
    adantr
    #
    @3
    cN
    cK
    cle
    wbr
    #
    cK
    cM
    cle
    wbr
    #
    @6
    @2
    @9
    @0
    cN
    cK
    eluzle
    adantl
    @0
    @10
    @2
    cK
    cM
    eluzle
    adantr
    @3
    @4
    cK
    cz
    wcel
    #
    @5
    @9
    @10
    wa
    @6
    wi
    @7
    @2
    @11
    @0
    cN
    cK
    eluzelz
    adantl
    @8
    cN
    cK
    cM
    zletr
    syl3anc
    mp2and
    cN
    cM
    eluz2
    syl3anbrc
end
