include "csr.mm"
include "wcel.mm"
include "wa.mm"
include "cstf.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "stafval.mm"
include "adantl.mm"
include "wf1o.mm"
include "wf.mm"
include "srngf1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"

theorem srngcl
  let cB: class B
  let cR: class R
  let c.as: class .*
  let cX: class X
  assume srngcl.i: |- .* = ( *r ` R )
  assume srngcl.b: |- B = ( Base ` R )


  assert |- ( ( R e. *Ring /\ X e. B ) -> ( .* ` X ) e. B )

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
    cX
    cR
    cstf
    cfv
    #
    cfv
    #
    cX
    c.as
    cfv
    #
    cB
    @1
    @3
    @4
    wceq
    @0
    cX
    cB
    cR
    @2
    c.as
    srngcl.b
    srngcl.i
    @2
    eqid
    #
    stafval
    adantl
    @0
    cB
    cB
    cX
    @2
    @0
    cB
    cB
    @2
    wf1o
    cB
    cB
    @2
    wf
    cB
    cR
    @2
    @5
    srngcl.b
    srngf1o
    cB
    cB
    @2
    f1of
    syl
    ffvelrnda
    eqeltrrd
end
