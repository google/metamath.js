include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cco1.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "cif.mm"
include "cn0.mm"
include "cvv.mm"
include "cmpt.mm"
include "coe1scl.mm"
include "adantr.mm"
include "weq.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "adantl.mm"
include "wb.mm"
include "eqeq1.mm"
include "notbid.mm"
include "mpbird.mm"
include "iffalsed.mm"
include "nnnn0.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvmptd.mm"
include "ralrimiva.mm"

theorem cply1coe0
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cK: class K
  let c.0: class .0.
  let vk: setvar k
  assume cply1coe0.k: |- K = ( Base ` R )
  assume cply1coe0.0: |- .0. = ( 0g ` R )
  assume cply1coe0.p: |- P = ( Poly1 ` R )
  assume cply1coe0.b: |- B = ( Base ` P )
  assume cply1coe0.a: |- A = ( algSc ` P )

  disjoint K n
  disjoint R n
  disjoint S n
  disjoint A k
  disjoint K k
  disjoint k n
  disjoint P k
  disjoint R k
  disjoint S k
  disjoint .0. k
  assert |- ( ( R e. Ring /\ S e. K ) -> A. n e. NN ( ( coe1 ` ( A ` S ) ) ` n ) = .0. )

  proof
    cR
    crg
    wcel
    cS
    cK
    wcel
    wa
    #
    vn
    cv
    #
    cS
    cA
    cfv
    cco1
    cfv
    #
    cfv
    c.0
    wceq
    vn
    cn
    @0
    @1
    cn
    wcel
    #
    wa
    #
    vk
    @1
    vk
    cv
    #
    cc0
    wceq
    #
    cS
    c.0
    cif
    #
    c.0
    cn0
    @2
    cvv
    @0
    @2
    vk
    cn0
    @7
    cmpt
    wceq
    @3
    vk
    cA
    cP
    cR
    cK
    cS
    c.0
    cply1coe0.p
    cply1coe0.a
    cply1coe0.k
    cply1coe0.0
    coe1scl
    adantr
    @4
    vk
    vn
    weq
    #
    wa
    #
    @6
    cS
    c.0
    @9
    @6
    wn
    #
    @1
    cc0
    wceq
    #
    wn
    #
    @4
    @12
    @8
    @3
    @12
    @0
    @3
    @1
    cc0
    @1
    nnne0
    neneqd
    adantl
    adantr
    @8
    @10
    @12
    wb
    @4
    @8
    @6
    @11
    @5
    @1
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @3
    @1
    cn0
    wcel
    @0
    @1
    nnnn0
    adantl
    c.0
    cvv
    wcel
    @4
    c.0
    cR
    c0g
    cfv
    cvv
    cply1coe0.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fvmptd
    ralrimiva
end
