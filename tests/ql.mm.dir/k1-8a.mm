include "wo.mm"
include "wa.mm"
include "leo.mm"
include "ler2an.mm"
include "wn.mm"
include "lelor.mm"
include "leran.mm"
include "ax-a1.mm"
include "ror.mm"
include "ran.mm"
include "k1-6.mm"
include "tr.mm"
include "cm.mm"
include "df2le2.mm"
include "3tr.mm"
include "lbtr.mm"
include "lebi.mm"

theorem k1-8a
  let wvc: term c
  let wvx: term x
  let wvy: term y
  assume k1-8a.1: |- x ' = ( ( x ' ^ c ) v ( x ' ^ c ' ) )
  assume k1-8a.2: |- x =< c
  assume k1-8a.3: |- y =< c '


  assert |- x = ( ( x v y ) ^ c )

  proof
    wvx
    wvx
    wvy
    wo
    #
    wvc
    wa
    #
    wvx
    @0
    wvc
    wvx
    wvy
    leo
    k1-8a.2
    ler2an
    @1
    wvx
    wvc
    wn
    #
    wo
    #
    wvc
    wa
    #
    wvx
    @0
    @3
    wvc
    wvy
    @2
    wvx
    k1-8a.3
    lelor
    leran
    @4
    wvx
    wn
    #
    wn
    #
    @2
    wo
    #
    wvc
    wa
    #
    wvx
    wvc
    wa
    #
    wvx
    @3
    @7
    wvc
    wvx
    @6
    @2
    wvx
    ax-a1
    #
    ror
    ran
    @9
    @8
    @9
    @6
    wvc
    wa
    @8
    wvx
    @6
    wvc
    @10
    ran
    wvc
    @5
    k1-8a.1
    k1-6
    tr
    cm
    wvx
    wvc
    k1-8a.2
    df2le2
    3tr
    lbtr
    lebi
end
