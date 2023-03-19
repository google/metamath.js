include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cco1.mm"
include "wceq.mm"
include "ply1sclid.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "ply1sclcl.mm"
include "deg1le0.mm"
include "syldan.mm"
include "mpbird.mm"

theorem deg1sclle
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  assume deg1sclle.d: |- D = ( deg1 ` R )
  assume deg1sclle.p: |- P = ( Poly1 ` R )
  assume deg1sclle.k: |- K = ( Base ` R )
  assume deg1sclle.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. K ) -> ( D ` ( A ` F ) ) <_ 0 )

  proof
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    wa
    #
    cF
    cA
    cfv
    #
    cD
    cfv
    cc0
    cle
    wbr
    #
    @3
    cc0
    @3
    cco1
    cfv
    cfv
    #
    cA
    cfv
    wceq
    #
    @2
    cF
    @5
    cA
    cA
    cP
    cR
    cK
    cF
    deg1sclle.p
    deg1sclle.a
    deg1sclle.k
    ply1sclid
    fveq2d
    @0
    @1
    @3
    cP
    cbs
    cfv
    #
    wcel
    @4
    @6
    wb
    cA
    @7
    cP
    cR
    cF
    cK
    deg1sclle.p
    deg1sclle.a
    deg1sclle.k
    @7
    eqid
    #
    ply1sclcl
    cA
    @7
    cD
    cP
    cR
    @3
    deg1sclle.d
    deg1sclle.p
    @8
    deg1sclle.a
    deg1le0
    syldan
    mpbird
end
