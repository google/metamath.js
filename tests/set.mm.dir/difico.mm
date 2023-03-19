include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cdif.mm"
include "cun.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "icodisj.mm"
include "undif4.mm"
include "syl.mm"
include "adantr.mm"
include "difid.mm"
include "uneq2i.mm"
include "un0.mm"
include "eqtri.mm"
include "a1i.mm"
include "icoun.mm"
include "difeq1d.mm"
include "3eqtr3rd.mm"

theorem difico
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A <_ B /\ B <_ C ) ) -> ( ( A [,) C ) \ ( B [,) C ) ) = ( A [,) B ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    w3a
    #
    cA
    cB
    cle
    wbr
    cB
    cC
    cle
    wbr
    wa
    #
    wa
    #
    cA
    cB
    cico
    co
    #
    cB
    cC
    cico
    co
    #
    @4
    cdif
    #
    cun
    #
    @3
    @4
    cun
    #
    @4
    cdif
    #
    @3
    cA
    cC
    cico
    co
    #
    @4
    cdif
    @0
    @6
    @8
    wceq
    #
    @1
    @0
    @3
    @4
    cin
    c0
    wceq
    @10
    cA
    cB
    cC
    icodisj
    @3
    @4
    @4
    undif4
    syl
    adantr
    @6
    @3
    wceq
    @2
    @6
    @3
    c0
    cun
    @3
    @5
    c0
    @3
    @4
    difid
    uneq2i
    @3
    un0
    eqtri
    a1i
    @2
    @7
    @9
    @4
    cA
    cB
    cC
    icoun
    difeq1d
    3eqtr3rd
end
