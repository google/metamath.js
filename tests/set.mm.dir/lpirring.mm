include "clpir.mm"
include "wcel.mm"
include "crg.mm"
include "clidl.mm"
include "cfv.mm"
include "clpidl.mm"
include "wceq.mm"
include "eqid.mm"
include "islpir.mm"
include "simplbi.mm"

theorem lpirring
  let cR: class R


  assert |- ( R e. LPIR -> R e. Ring )

  proof
    cR
    clpir
    wcel
    cR
    crg
    wcel
    cR
    clidl
    cfv
    #
    cR
    clpidl
    cfv
    #
    wceq
    @1
    cR
    @0
    @1
    eqid
    @0
    eqid
    islpir
    simplbi
end
