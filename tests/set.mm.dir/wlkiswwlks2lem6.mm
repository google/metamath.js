include "cuspgr.mm"
include "wcel.mm"
include "cword.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "crn.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "cdm.mm"
include "cfz.mm"
include "wf.mm"
include "wceq.mm"
include "wa.mm"
include "wlkiswwlks2lem5.mm"
include "imp.mm"
include "wlkiswwlks2lem3.mm"
include "3adant1.mm"
include "adantr.mm"
include "wlkiswwlks2lem4.mm"
include "3jca.mm"
include "ex.mm"

theorem wlkiswwlks2lem6
  let vx: setvar x
  let cP: class P
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cI: class I
  assume wlkiswwlks2lem.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) )
  assume wlkiswwlks2lem.e: |- E = ( iEdg ` G )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint F i
  disjoint G i
  disjoint P i
  disjoint V i
  disjoint i x
  disjoint E i
  disjoint G x
  disjoint I x
  assert |- ( ( G e. USPGraph /\ P e. Word V /\ 1 <_ ( # ` P ) ) -> ( A. i e. ( 0 ..^ ( ( # ` P ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E -> ( F e. Word dom E /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. i e. ( 0 ..^ ( # ` F ) ) ( E ` ( F ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) ) )

  proof
    cG
    cuspgr
    wcel
    #
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
    w3a
    #
    vi
    cv
    #
    cP
    cfv
    @5
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    cE
    crn
    wcel
    vi
    cc0
    @2
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cF
    cE
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    @5
    cF
    cfv
    cE
    cfv
    @6
    wceq
    vi
    cc0
    @9
    cfzo
    co
    wral
    #
    w3a
    @4
    @7
    wa
    @8
    @10
    @11
    @4
    @7
    @8
    vx
    cP
    vi
    cE
    cF
    cG
    cV
    wlkiswwlks2lem.f
    wlkiswwlks2lem.e
    wlkiswwlks2lem5
    imp
    @4
    @10
    @7
    @1
    @3
    @10
    @0
    vx
    cP
    cE
    cF
    cV
    wlkiswwlks2lem.f
    wlkiswwlks2lem3
    3adant1
    adantr
    @4
    @7
    @11
    vx
    cP
    vi
    cE
    cF
    cG
    cV
    wlkiswwlks2lem.f
    wlkiswwlks2lem.e
    wlkiswwlks2lem4
    imp
    3jca
    ex
end
