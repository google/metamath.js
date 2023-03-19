include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "cpfx.mm"
include "simp1.mm"
include "nn0fz0.mm"
include "fzelp1.mm"
include "sylbi.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "pfxlen.mm"
include "syl2anc.mm"

theorem pfxlen0
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. NN0 /\ ( # ` W ) = ( L + 1 ) ) -> ( # ` ( W prefix L ) ) = L )

  proof
    cW
    cV
    cword
    wcel
    #
    cL
    cn0
    wcel
    #
    cW
    chash
    cfv
    #
    cL
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @0
    cL
    cc0
    @2
    cfz
    co
    #
    wcel
    #
    cW
    cL
    cpfx
    co
    chash
    cfv
    cL
    wceq
    @0
    @1
    @4
    simp1
    @5
    @7
    cL
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @1
    @0
    @9
    @4
    @1
    cL
    cc0
    cL
    cfz
    co
    wcel
    @9
    cL
    nn0fz0
    cL
    cc0
    cL
    fzelp1
    sylbi
    3ad2ant2
    @4
    @0
    @7
    @9
    wb
    @1
    @4
    @6
    @8
    cL
    @2
    @3
    cc0
    cfz
    oveq2
    eleq2d
    3ad2ant3
    mpbird
    cV
    cW
    cL
    pfxlen
    syl2anc
end
