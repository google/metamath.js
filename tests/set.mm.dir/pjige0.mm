include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cc0.mm"
include "cpjh.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "h0elch.mm"
include "elimel.mm"
include "pjige0i.mm"
include "dedth.mm"
include "imp.mm"

theorem pjige0
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> 0 <_ ( ( ( projh ` H ) ` A ) .ih A ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cc0
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    csp
    co
    #
    cle
    wbr
    #
    @0
    @1
    @5
    wi
    @1
    cc0
    cA
    @0
    cH
    c0h
    cif
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    csp
    co
    #
    cle
    wbr
    #
    wi
    cH
    c0h
    cH
    @6
    wceq
    #
    @5
    @10
    @1
    @11
    @4
    @9
    cc0
    cle
    @11
    @3
    @8
    cA
    csp
    @11
    cA
    @2
    @7
    cH
    @6
    cpjh
    fveq2
    fveq1d
    oveq1d
    breq2d
    imbi2d
    cA
    @6
    cH
    c0h
    cch
    h0elch
    elimel
    pjige0i
    dedth
    imp
end
