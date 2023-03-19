include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "chssii.mm"
include "occon3.mm"
include "mp2an.mm"

theorem chsscon2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A C_ ( _|_ ` B ) <-> B C_ ( _|_ ` A ) )

  proof
    cA
    chil
    wss
    cB
    chil
    wss
    cA
    cB
    cort
    cfv
    wss
    cB
    cA
    cort
    cfv
    wss
    wb
    cA
    ch0le.1
    chssii
    cB
    chjcl.2
    chssii
    cA
    cB
    occon3
    mp2an
end
