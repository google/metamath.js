include "csr.mm"
include "wcel.mm"
include "coppr.mm"
include "cfv.mm"
include "crh.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "eqid.mm"
include "issrng.mm"
include "simprbi.mm"

theorem srngcnv
  let cR: class R
  let c.as: class .*
  assume srngcnv.i: |- .* = ( *rf ` R )


  assert |- ( R e. *Ring -> .* = `' .* )

  proof
    cR
    csr
    wcel
    c.as
    cR
    cR
    coppr
    cfv
    #
    crh
    co
    wcel
    c.as
    c.as
    ccnv
    wceq
    cR
    c.as
    @0
    @0
    eqid
    srngcnv.i
    issrng
    simprbi
end
