include "wss.mm"
include "wel.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "ssralv.mm"
include "ss2abdv.mm"
include "dfint2.mm"
include "3sstr4g.mm"

theorem intss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( A C_ B -> |^| B C_ |^| A )

  proof
    cA
    cB
    wss
    #
    vy
    vx
    wel
    #
    vx
    cB
    wral
    #
    vy
    cab
    @1
    vx
    cA
    wral
    #
    vy
    cab
    cB
    cint
    cA
    cint
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    ssralv
    ss2abdv
    vy
    vx
    cB
    dfint2
    vy
    vx
    cA
    dfint2
    3sstr4g
end
