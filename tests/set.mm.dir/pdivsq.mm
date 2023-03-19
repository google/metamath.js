include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "wb.mm"
include "zcn.mm"
include "sqvald.mm"
include "breq2d.mm"
include "adantl.mm"
include "wo.mm"
include "euclemma.mm"
include "3anidm23.mm"
include "oridm.mm"
include "syl6bb.mm"
include "bitr2d.mm"

theorem pdivsq
  let cP: class P
  let cM: class M


  assert |- ( ( P e. Prime /\ M e. ZZ ) -> ( P || M <-> P || ( M ^ 2 ) ) )

  proof
    cP
    cprime
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    cP
    cM
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    cP
    cM
    cM
    cmul
    co
    #
    cdvds
    wbr
    #
    cP
    cM
    cdvds
    wbr
    #
    @1
    @4
    @6
    wb
    @0
    @1
    @3
    @5
    cP
    cdvds
    @1
    cM
    cM
    zcn
    sqvald
    breq2d
    adantl
    @2
    @6
    @7
    @7
    wo
    #
    @7
    @0
    @1
    @6
    @8
    wb
    cP
    cM
    cM
    euclemma
    3anidm23
    @7
    oridm
    syl6bb
    bitr2d
end
