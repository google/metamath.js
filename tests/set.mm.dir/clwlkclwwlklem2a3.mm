include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clsw.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "lsw.mm"
include "adantr.mm"
include "clwlkclwwlklem2a2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem clwlkclwwlklem2a3
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cV: class V
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  disjoint E x
  disjoint V x
  assert |- ( ( P e. Word V /\ 2 <_ ( # ` P ) ) -> ( P ` ( # ` F ) ) = ( lastS ` P ) )

  proof
    cP
    cV
    cword
    #
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cP
    clsw
    cfv
    #
    @2
    c1
    cmin
    co
    #
    cP
    cfv
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    @1
    @5
    @7
    wceq
    @3
    cP
    @0
    lsw
    adantr
    @4
    @6
    @8
    cP
    @4
    @8
    @6
    vx
    cP
    cE
    cF
    cV
    clwlkclwwlklem2.f
    clwlkclwwlklem2a2
    eqcomd
    fveq2d
    eqtr2d
end
