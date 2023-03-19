include "caa.mm"
include "wcel.mm"
include "cmpaa.mm"
include "cfv.mm"
include "cq.mm"
include "cply.mm"
include "cdgr.mm"
include "cdgraa.mm"
include "wceq.mm"
include "cc0.mm"
include "ccoe.mm"
include "c1.mm"
include "w3a.mm"
include "mpaalem.mm"
include "simpld.mm"

theorem mpaacl
  let cA: class A
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P


  assert |- ( A e. AA -> ( minPolyAA ` A ) e. ( Poly ` QQ ) )

  proof
    cA
    caa
    wcel
    cA
    cmpaa
    cfv
    #
    cq
    cply
    cfv
    wcel
    @0
    cdgr
    cfv
    cA
    cdgraa
    cfv
    #
    wceq
    cA
    @0
    cfv
    cc0
    wceq
    @1
    @0
    ccoe
    cfv
    cfv
    c1
    wceq
    w3a
    cA
    mpaalem
    simpld
end
