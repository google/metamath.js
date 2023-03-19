include "csr.mm"
include "wcel.mm"
include "crh.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "issrng.mm"
include "simplbi.mm"

theorem srngrhm
  let cR: class R
  let c.as: class .*
  let cO: class O
  let vi: setvar i
  let vr: setvar r
  assume issrng.o: |- O = ( oppR ` R )
  assume issrng.i: |- .* = ( *rf ` R )


  assert |- ( R e. *Ring -> .* e. ( R RingHom O ) )

  proof
    cR
    csr
    wcel
    c.as
    cR
    cO
    crh
    co
    wcel
    c.as
    c.as
    ccnv
    wceq
    cR
    c.as
    cO
    issrng.o
    issrng.i
    issrng
    simplbi
end
