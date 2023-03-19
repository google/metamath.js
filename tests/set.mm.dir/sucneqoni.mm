include "wne.mm"
include "wtru.mm"
include "csuc.mm"
include "wceq.mm"
include "a1i.mm"
include "con0.mm"
include "wcel.mm"
include "sucneqond.mm"
include "trud.mm"

theorem sucneqoni
  let cX: class X
  let cY: class Y
  assume sucneqoni.1: |- X = suc Y
  assume sucneqoni.2: |- Y e. On


  assert |- X =/= Y

  proof
    cX
    cY
    wne
    wtru
    cX
    cY
    cX
    cY
    csuc
    wceq
    wtru
    sucneqoni.1
    a1i
    cY
    con0
    wcel
    wtru
    sucneqoni.2
    a1i
    sucneqond
    trud
end
