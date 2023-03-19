include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wf.mm"
include "wlkiswwlks2lem1.mm"
include "wi.mm"
include "cfzo.mm"
include "cn0.mm"
include "wrdf.mm"
include "lencl.mm"
include "cz.mm"
include "nn0z.mm"
include "fzoval.mm"
include "syl.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "sylan9eq.mm"
include "feq2d.mm"
include "biimpcd.mm"
include "expd.mm"
include "sylc.mm"
include "adantr.mm"
include "mpd.mm"

theorem wlkiswwlks2lem3
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cV: class V
  let cI: class I
  assume wlkiswwlks2lem.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint I x
  assert |- ( ( P e. Word V /\ 1 <_ ( # ` P ) ) -> P : ( 0 ... ( # ` F ) ) --> V )

  proof
    cP
    cV
    cword
    wcel
    #
    c1
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    cF
    chash
    cfv
    #
    @1
    c1
    cmin
    co
    #
    wceq
    #
    cc0
    @3
    cfz
    co
    #
    cV
    cP
    wf
    #
    vx
    cP
    cE
    cF
    cV
    wlkiswwlks2lem.f
    wlkiswwlks2lem1
    @0
    @5
    @7
    wi
    #
    @2
    @0
    cc0
    @1
    cfzo
    co
    #
    cV
    cP
    wf
    #
    @1
    cn0
    wcel
    #
    @8
    cV
    cP
    wrdf
    cV
    cP
    lencl
    @10
    @11
    @5
    @7
    @11
    @5
    wa
    #
    @10
    @7
    @12
    @9
    @6
    cV
    cP
    @11
    @5
    @9
    cc0
    @4
    cfz
    co
    #
    @6
    @11
    @1
    cz
    wcel
    @9
    @13
    wceq
    @1
    nn0z
    cc0
    @1
    fzoval
    syl
    @13
    @6
    wceq
    @4
    @3
    @4
    @3
    cc0
    cfz
    oveq2
    eqcoms
    sylan9eq
    feq2d
    biimpcd
    expd
    sylc
    adantr
    mpd
end
