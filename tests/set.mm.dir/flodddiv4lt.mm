include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c4.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "simpl.mm"
include "4z.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "4dvdseven.mm"
include "con3i.mm"
include "adantl.mm"
include "fldivndvdslt.mm"
include "syl3anc.mm"

theorem flodddiv4lt
  let cN: class N


  assert |- ( ( N e. ZZ /\ -. 2 || N ) -> ( |_ ` ( N / 4 ) ) < ( N / 4 ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    @0
    c4
    cz
    wcel
    #
    c4
    cc0
    wne
    #
    wa
    #
    c4
    cN
    cdvds
    wbr
    #
    wn
    #
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
    @9
    clt
    wbr
    @0
    @2
    simpl
    @6
    @3
    @4
    @5
    4z
    4ne0
    pm3.2i
    a1i
    @2
    @8
    @0
    @7
    @1
    cN
    4dvdseven
    con3i
    adantl
    cN
    c4
    fldivndvdslt
    syl3anc
end
