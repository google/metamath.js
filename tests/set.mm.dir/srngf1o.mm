include "csr.mm"
include "wcel.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "coppr.mm"
include "cfv.mm"
include "crh.mm"
include "co.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "srngrhm.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "srngcnv.mm"
include "fneq1d.mm"
include "mpbid.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem srngf1o
  let cB: class B
  let cR: class R
  let c.as: class .*
  assume srngcnv.i: |- .* = ( *rf ` R )
  assume srngf1o.b: |- B = ( Base ` R )


  assert |- ( R e. *Ring -> .* : B -1-1-onto-> B )

  proof
    cR
    csr
    wcel
    #
    c.as
    cB
    wfn
    #
    c.as
    ccnv
    #
    cB
    wfn
    #
    cB
    cB
    c.as
    wf1o
    @0
    c.as
    cR
    cR
    coppr
    cfv
    #
    crh
    co
    wcel
    cB
    @4
    cbs
    cfv
    #
    c.as
    wf
    @1
    cR
    c.as
    @4
    @4
    eqid
    srngcnv.i
    srngrhm
    cB
    @5
    cR
    @4
    c.as
    srngf1o.b
    @5
    eqid
    rhmf
    cB
    @5
    c.as
    ffn
    3syl
    #
    @0
    @1
    @3
    @6
    @0
    cB
    c.as
    @2
    cR
    c.as
    srngcnv.i
    srngcnv
    fneq1d
    mpbid
    cB
    cB
    c.as
    dff1o4
    sylanbrc
end
