include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "chil.mm"
include "wi.mm"
include "chssii.mm"
include "occon.mm"
include "mp2an.mm"
include "choccli.mm"
include "pjococi.mm"
include "3sstr3g.mm"
include "impbii.mm"

theorem chsscon3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A C_ B <-> ( _|_ ` B ) C_ ( _|_ ` A ) )

  proof
    cA
    cB
    wss
    #
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    #
    cA
    chil
    wss
    cB
    chil
    wss
    @0
    @3
    wi
    cA
    ch0le.1
    chssii
    cB
    chjcl.2
    chssii
    cA
    cB
    occon
    mp2an
    @3
    @2
    cort
    cfv
    #
    @1
    cort
    cfv
    #
    cA
    cB
    @1
    chil
    wss
    @2
    chil
    wss
    @3
    @4
    @5
    wss
    wi
    @1
    cB
    chjcl.2
    choccli
    chssii
    @2
    cA
    ch0le.1
    choccli
    chssii
    @1
    @2
    occon
    mp2an
    cA
    ch0le.1
    pjococi
    cB
    chjcl.2
    pjococi
    3sstr3g
    impbii
end
