include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "wfun.mm"
include "wss.mm"
include "cnx.mm"
include "cop.mm"
include "strssd.mm"
include "trud.mm"

theorem strss
  let cC: class C
  let cS: class S
  let cT: class T
  let cE: class E
  assume strss.t: |- T e. _V
  assume strss.f: |- Fun T
  assume strss.s: |- S C_ T
  assume strss.e: |- E = Slot ( E ` ndx )
  assume strss.n: |- <. ( E ` ndx ) , C >. e. S


  assert |- ( E ` T ) = ( E ` S )

  proof
    cT
    cE
    cfv
    cS
    cE
    cfv
    wceq
    wtru
    cC
    cS
    cT
    cE
    cvv
    strss.e
    cT
    cvv
    wcel
    wtru
    strss.t
    a1i
    cT
    wfun
    wtru
    strss.f
    a1i
    cS
    cT
    wss
    wtru
    strss.s
    a1i
    cnx
    cE
    cfv
    cC
    cop
    cS
    wcel
    wtru
    strss.n
    a1i
    strssd
    trud
end
