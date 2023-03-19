include "csr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cstf.mm"
include "wceq.mm"
include "srngcl.mm"
include "eqid.mm"
include "stafval.mm"
include "syl.mm"
include "ccnv.mm"
include "srngcnv.mm"
include "adantr.mm"
include "fveq1d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "srngf1o.mm"
include "f1ocnvfv1.mm"
include "sylan.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"

theorem srngnvl
  let cB: class B
  let cR: class R
  let c.as: class .*
  let cX: class X
  assume srngcl.i: |- .* = ( *r ` R )
  assume srngcl.b: |- B = ( Base ` R )


  assert |- ( ( R e. *Ring /\ X e. B ) -> ( .* ` ( .* ` X ) ) = X )

  proof
    cR
    csr
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.as
    cfv
    #
    cR
    cstf
    cfv
    #
    cfv
    #
    @3
    c.as
    cfv
    #
    cX
    @2
    @3
    cB
    wcel
    @5
    @6
    wceq
    cB
    cR
    c.as
    cX
    srngcl.i
    srngcl.b
    srngcl
    @3
    cB
    cR
    @4
    c.as
    srngcl.b
    srngcl.i
    @4
    eqid
    #
    stafval
    syl
    @2
    cX
    @4
    cfv
    #
    @4
    cfv
    @8
    @4
    ccnv
    #
    cfv
    #
    @5
    cX
    @2
    @8
    @4
    @9
    @0
    @4
    @9
    wceq
    @1
    cR
    @4
    @7
    srngcnv
    adantr
    fveq1d
    @2
    @8
    @3
    @4
    @1
    @8
    @3
    wceq
    @0
    cX
    cB
    cR
    @4
    c.as
    srngcl.b
    srngcl.i
    @7
    stafval
    adantl
    fveq2d
    @0
    cB
    cB
    @4
    wf1o
    @1
    @10
    cX
    wceq
    cB
    cR
    @4
    @7
    srngcl.b
    srngf1o
    cB
    cB
    cX
    @4
    f1ocnvfv1
    sylan
    3eqtr3d
    eqtr3d
end
