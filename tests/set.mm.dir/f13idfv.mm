include "cc0.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "wne.mm"
include "wf1.mm"
include "wf.mm"
include "cfv.mm"
include "wa.mm"
include "wb.mm"
include "0z.mm"
include "1z.mm"
include "2z.mm"
include "3pm3.2i.mm"
include "0ne1.mm"
include "0ne2.mm"
include "1ne2.mm"
include "cfz.mm"
include "co.mm"
include "ctp.mm"
include "fz0tp.mm"
include "eqtri.mm"
include "f13dfv.mm"
include "mp2an.mm"

theorem f13idfv
  let cA: class A
  let cB: class B
  let cF: class F
  assume f13idfv.a: |- A = ( 0 ... 2 )


  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ ( ( F ` 0 ) =/= ( F ` 1 ) /\ ( F ` 0 ) =/= ( F ` 2 ) /\ ( F ` 1 ) =/= ( F ` 2 ) ) ) )

  proof
    cc0
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    w3a
    cc0
    c1
    wne
    #
    cc0
    c2
    wne
    #
    c1
    c2
    wne
    #
    w3a
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    cc0
    cF
    cfv
    #
    c1
    cF
    cfv
    #
    wne
    @6
    c2
    cF
    cfv
    #
    wne
    @7
    @8
    wne
    w3a
    wa
    wb
    @0
    @1
    @2
    0z
    1z
    2z
    3pm3.2i
    @3
    @4
    @5
    0ne1
    0ne2
    1ne2
    3pm3.2i
    cA
    cB
    cz
    cF
    cz
    cz
    cc0
    c1
    c2
    cA
    cc0
    c2
    cfz
    co
    cc0
    c1
    c2
    ctp
    f13idfv.a
    fz0tp
    eqtri
    f13dfv
    mp2an
end
