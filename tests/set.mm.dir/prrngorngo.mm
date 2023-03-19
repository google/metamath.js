include "cprrng.mm"
include "wcel.mm"
include "crngo.mm"
include "c1st.mm"
include "cfv.mm"
include "cgi.mm"
include "csn.mm"
include "cpridl.mm"
include "eqid.mm"
include "isprrngo.mm"
include "simplbi.mm"

theorem prrngorngo
  let cR: class R


  assert |- ( R e. PrRing -> R e. RingOps )

  proof
    cR
    cprrng
    wcel
    cR
    crngo
    wcel
    cR
    c1st
    cfv
    #
    cgi
    cfv
    #
    csn
    cR
    cpridl
    cfv
    wcel
    cR
    @0
    @1
    @0
    eqid
    @1
    eqid
    isprrngo
    simplbi
end
